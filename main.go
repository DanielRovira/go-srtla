package main

import (
	"crypto/rand"
	"encoding/binary"
	"flag"
	"fmt"
	"io"
	"log"
	mathrand "math/rand"
	"net"
	"sync"
	"time"
)

const (
	MTU = 1500

	SRTTypeHandshake = 0x8000
	SRTTypeACK       = 0x8002
	SRTTypeNAK       = 0x8003
	SRTTypeShutdown  = 0x8005

	SRTMinLen = 16

	SRTLATypeKeepalive = 0x9000
	SRTLATypeACK       = 0x9100
	SRTLATypeReg1      = 0x9200
	SRTLATypeReg2      = 0x9201
	SRTLATypeReg3      = 0x9202
	SRTLATypeRegErr    = 0x9210
	SRTLATypeRegNGP    = 0x9211

	SRTLAIDLen   = 256
	SRTLAReg1Len = 2 + SRTLAIDLen
	SRTLAReg2Len = 2 + SRTLAIDLen
	SRTLAReg3Len = 2

	RecvACKInterval = 10 // number of pkts before sending SRTLA ACK

	MaxConnsPerGroup = 32
	MaxGroups        = 200

	CleanupPeriod = 3 * time.Second
	GroupTimeout  = 15 * time.Second
	ConnTimeout   = 15 * time.Second

	SendBufSize = 300 * 1024 * 1024 // 100 MB (matches C++)
	RecvBufSize = 300 * 1024 * 1024
)

func constantTimeCompare(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	var diff byte
	for i := 0; i < len(a); i++ {
		diff |= a[i] ^ b[i]
	}
	return diff == 0
}

func randomBytes(n int) []byte {
	b := make([]byte, n)
	if _, err := io.ReadFull(rand.Reader, b); err != nil {
		log.Printf("warning: crypto/rand failed (%v); falling back to pseudo-rand", err)
		for i := range b {
			b[i] = byte(mathrand.Intn(256))
		}
	}
	return b
}

func udpAddrEqual(a, b *net.UDPAddr) bool {
	if a == nil || b == nil {
		return false
	}
	return a.IP.Equal(b.IP) && a.Port == b.Port
}

type OrderedPacket struct {
    seqNo   int32
    data    []byte
    time    time.Time
}

type Conn struct {
	addr     *net.UDPAddr
	lastRcvd time.Time

	// SRTLA ACK tracking
	recvLog [RecvACKInterval]uint32
	recvIdx int
}

type Group struct {
	id        [SRTLAIDLen]byte
	conns     []*Conn
	createdAt time.Time
	srtSock   *net.UDPConn // connection to downstream SRT server
	lastAddr  *net.UDPAddr // most recently active client addr
	mu        sync.Mutex   // protects conns, lastAddr, srtSock
	reorderBuffer map[int32][]byte  // Buffer de reordenação
    nextSeq       int32              // Próximo sequência esperada
}

var (
	groupsMu sync.RWMutex
	groups   []*Group

	srtlaSock *net.UDPConn
	srtAddr   *net.UDPAddr // resolved downstream SRT server address
)

func be16(b []byte) uint16 { return binary.BigEndian.Uint16(b) }
func be32(b []byte) uint32 { return binary.BigEndian.Uint32(b) }

func getSRTType(pkt []byte) uint16 {
	if len(pkt) < 2 {
		return 0
	}
	return be16(pkt[:2])
}

func getSRTSeqNo(pkt []byte) int32 {
	if len(pkt) < 4 {
		return -1
	}
	sn := be32(pkt[:4])
	if sn&(1<<31) != 0 {
		return -1 // control packet
	}
	return int32(sn)
}

func isSRTAck(pkt []byte) bool         { return getSRTType(pkt) == SRTTypeACK }
func isSRTNak(pkt []byte) bool         { return getSRTType(pkt) == SRTTypeNAK }
func isSRTLAKeepalive(pkt []byte) bool { return getSRTType(pkt) == SRTLATypeKeepalive }

func isSRTLAReg1(pkt []byte) bool {
	return len(pkt) == SRTLAReg1Len && getSRTType(pkt) == SRTLATypeReg1
}
func isSRTLAReg2(pkt []byte) bool {
	return len(pkt) == SRTLAReg2Len && getSRTType(pkt) == SRTLATypeReg2
}

func findGroupByID(id []byte) *Group {
	groupsMu.RLock()
	defer groupsMu.RUnlock()
	for _, g := range groups {
		if constantTimeCompare(g.id[:], id) {
			return g
		}
	}
	return nil
}

func findByAddr(addr *net.UDPAddr) (g *Group, c *Conn) {
	groupsMu.RLock()
	defer groupsMu.RUnlock()
	for _, gr := range groups {
		gr.mu.Lock()
		for _, conn := range gr.conns {
			if udpAddrEqual(conn.addr, addr) {
				gr.mu.Unlock()
				return gr, conn
			}
		}
		if udpAddrEqual(gr.lastAddr, addr) {
			gr.mu.Unlock()
			return gr, nil
		}
		gr.mu.Unlock()
	}
	return nil, nil
}

func newGroup(clientID []byte) *Group {
	var g Group
	g.createdAt = time.Now()

	copy(g.id[:SRTLAIDLen/2], clientID)
	copy(g.id[SRTLAIDLen/2:], randomBytes(SRTLAIDLen/2))
	return &g
}

func sendRegErr(addr *net.UDPAddr) {
	var header [2]byte
	binary.BigEndian.PutUint16(header[:], SRTLATypeRegErr)
	_, _ = srtlaSock.WriteToUDP(header[:], addr)
}

func registerGroup(addr *net.UDPAddr, pkt []byte) {
	if len(groups) >= MaxGroups {
		log.Printf("[%s] registration failed: max groups reached", addr)
		sendRegErr(addr)
		return
	}

	if g, _ := findByAddr(addr); g != nil {
		log.Printf("[%s] registration failed: addr already in group", addr)
		sendRegErr(addr)
		return
	}

	clientID := make([]byte, SRTLAIDLen/2)
	copy(clientID, pkt[2:])
	g := newGroup(clientID)

	g.lastAddr = addr

	out := make([]byte, SRTLAReg2Len)
	binary.BigEndian.PutUint16(out[:2], SRTLATypeReg2)
	copy(out[2:], g.id[:])

	if _, err := srtlaSock.WriteToUDP(out, addr); err != nil {
		log.Printf("[%s] registration failed: %v", addr, err)
		return
	}

	groupsMu.Lock()
	groups = append(groups, g)
	groupsMu.Unlock()

	log.Printf("[%s] [group %p] registered", addr, g)
}

func registerConn(addr *net.UDPAddr, pkt []byte) {
	id := pkt[2:]
	g := findGroupByID(id)

	// SE NÃO EXISTIR GRUPO, CRIA UM NOVO AUTOMATICAMENTE
	if g == nil {
		log.Printf("[%s] grupo não encontrado para ID %x, recriando automaticamente...", addr, id)

		// Verifica limite máximo de grupos
		groupsMu.Lock()
		if len(groups) >= MaxGroups {
			groupsMu.Unlock()
			log.Printf("[%s] não foi possível recriar: máximo de grupos atingido", addr)
			var hdr [2]byte
			binary.BigEndian.PutUint16(hdr[:], SRTLATypeRegNGP)
			srtlaSock.WriteToUDP(hdr[:], addr)
			return
		}

		// Cria novo grupo com o ID recebido
		g = &Group{}
		g.createdAt = time.Now()
		copy(g.id[:], id[:SRTLAIDLen])

		// Adiciona à lista de grupos
		groups = append(groups, g)
		groupsMu.Unlock()

		// Envia resposta REG2 confirmando o novo grupo
		out := make([]byte, SRTLAReg2Len)
		binary.BigEndian.PutUint16(out[:2], SRTLATypeReg2)
		copy(out[2:], g.id[:])
		srtlaSock.WriteToUDP(out, addr)

		log.Printf("[%s] [group %p] grupo recriado com sucesso após timeout", addr, g)
		// Continua a execução para registrar a conexão
	}

	// Verifica se o endereço já está em outro grupo
	if tmp, _ := findByAddr(addr); tmp != nil && tmp != g {
		sendRegErr(addr)
		log.Printf("[%s] [group %p] falha no registro: endereço em outro grupo", addr, g)
		return
	}

	// Registra a conexão
	var already bool
	g.mu.Lock()
	for _, c := range g.conns {
		if udpAddrEqual(c.addr, addr) {
			already = true
			break
		}
	}

	if !already {
		if len(g.conns) >= MaxConnsPerGroup {
			g.mu.Unlock()
			sendRegErr(addr)
			log.Printf("[%s] [group %p] falha no registro: muitas conexões", addr, g)
			return
		}
		g.conns = append(g.conns, &Conn{addr: addr, lastRcvd: time.Now()})
	}

	g.lastAddr = addr
	g.mu.Unlock()

	// Envia REG3 confirmando conexão
	var hdr [2]byte
	binary.BigEndian.PutUint16(hdr[:], SRTLATypeReg3)
	srtlaSock.WriteToUDP(hdr[:], addr)

	log.Printf("[%s] [group %p] conexão registrada com sucesso", addr, g)
}

func startSRTReader(g *Group) {
	go func() {
		buf := make([]byte, MTU)
		for {
			g.mu.Lock()
			conn := g.srtSock
			g.mu.Unlock()
			if conn == nil {
				return
			}
			n, err := conn.Read(buf)
			if err != nil {
				log.Printf("[group %p] SRT socket read error: %v", g, err)
				removeGroup(g)
				return
			}
			handleSRTData(g, buf[:n])
		}
	}()
}

func sendToClients(g *Group, pkt []byte) {
	if isSRTAck(pkt) || isSRTNak(pkt) {
		// Broadcast ACK/NAK para todos os clientes
		g.mu.Lock()
		conns := make([]*Conn, len(g.conns))
		copy(conns, g.conns)
		g.mu.Unlock()
		for _, c := range conns {
			if _, err := srtlaSock.WriteToUDP(pkt, c.addr); err != nil {
				log.Printf("[%s] [group %p] failed to fwd SRT ACK/NAK: %v", c.addr, g, err)
			}
		}
	} else {
		// Envia para o último cliente ativo
		g.mu.Lock()
		dst := g.lastAddr
		g.mu.Unlock()
		if dst != nil {
			if _, err := srtlaSock.WriteToUDP(pkt, dst); err != nil {
				log.Printf("[%s] [group %p] failed to fwd SRT pkt: %v", dst, g, err)
			}
		}
	}
}

func handleSRTData(g *Group, pkt []byte) {
    // Extrai número de sequência
    seqNo := getSRTSeqNo(pkt)
    if seqNo < 0 {
        // Pacote de controle, envia imediatamente
        sendToClients(g, pkt)
        return
    }
    
    // Adiciona ao buffer de reordenação
    g.mu.Lock()
    if g.reorderBuffer == nil {
        g.reorderBuffer = make(map[int32][]byte)
    }
    g.reorderBuffer[seqNo] = pkt
    
    // Envia pacotes em ordem
    for {
        data, ok := g.reorderBuffer[g.nextSeq]
        if !ok {
            break
        }
        sendToClients(g, data)
        delete(g.reorderBuffer, g.nextSeq)
        g.nextSeq++
    }
    g.mu.Unlock()
}

func registerPacket(g *Group, c *Conn, sn int32) {
	idx := c.recvIdx + 1
	if idx <= 0 || idx > RecvACKInterval {
		idx = 1
	}
	c.recvIdx = idx
	c.recvLog[idx-1] = uint32(sn)

	if c.recvIdx == RecvACKInterval {
		// Build SRTLA ACK: 4-byte header + 10 * 4-byte sequence numbers
		var ack [4 + RecvACKInterval*4]byte
		binary.BigEndian.PutUint32(ack[:4], uint32(SRTLATypeACK)<<16)
		for i := 0; i < RecvACKInterval; i++ {
			binary.BigEndian.PutUint32(ack[4+i*4:], c.recvLog[i])
		}
		if _, err := srtlaSock.WriteToUDP(ack[:], c.addr); err != nil {
			log.Printf("[%s] [group %p] failed to send SRTLA ACK: %v", c.addr, g, err)
		}
		c.recvIdx = 0
	}
}

func handleSRTLAIncoming(pkt []byte, addr *net.UDPAddr) {
	if isSRTLAReg1(pkt) {
		registerGroup(addr, pkt)
		return
	}
	if isSRTLAReg2(pkt) {
		registerConn(addr, pkt)
		return
	}

	g, c := findByAddr(addr)
	if g == nil || c == nil {
		return
	}

	g.mu.Lock()
	c.lastRcvd = time.Now()
	g.lastAddr = addr
	g.mu.Unlock()

	if isSRTLAKeepalive(pkt) {
		srtlaSock.WriteToUDP(pkt, addr)
		return
	}

	if len(pkt) < SRTMinLen {
		return
	}

	// Ensure SRT downstream socket exists
	g.mu.Lock()
	if g.srtSock == nil {
		conn, err := net.DialUDP("udp", nil, srtAddr)
		if err != nil {
			g.mu.Unlock()
			log.Printf("[group %p] failed to dial SRT server: %v", g, err)
			removeGroup(g)
			return
		}
		_ = conn.SetReadBuffer(RecvBufSize)
		_ = conn.SetWriteBuffer(SendBufSize)
		g.srtSock = conn
		g.mu.Unlock()
		startSRTReader(g)
		log.Printf("[group %p] created SRT socket (local %s)", g, conn.LocalAddr())
	} else {
		g.mu.Unlock()
	}

	g.mu.Lock()
	srtConn := g.srtSock
	g.mu.Unlock()
	if srtConn == nil {
		return
	}

	// Track sequence number and send SRTLA ACK every RecvACKInterval packets
	sn := getSRTSeqNo(pkt)
	if sn >= 0 {
		g.mu.Lock()
		registerPacket(g, c, sn)
		g.mu.Unlock()
	}

	_, err := srtConn.Write(pkt)
	if err != nil {
		log.Printf("[group %p] failed to fwd SRTLA pkt: %v", g, err)
		removeGroup(g)
	}
}

func cleanup() {
	now := time.Now()

	groupsMu.Lock()
	defer groupsMu.Unlock()

	var newGroups []*Group
	for _, g := range groups {
		g.mu.Lock()
		var newConns []*Conn
		for _, c := range g.conns {
			if now.Sub(c.lastRcvd) < ConnTimeout {
				newConns = append(newConns, c)
			} else {
				log.Printf("[%s] [group %p] connection timed out", c.addr, g)
			}
		}
		if len(newConns) != len(g.conns) {
			g.conns = newConns
		}

		keep := true
		if len(g.conns) == 0 && now.Sub(g.createdAt) > GroupTimeout {
			keep = false
		}

		if !keep {
			// Close while still holding g.mu to avoid double-lock in close()
			if g.srtSock != nil {
				g.srtSock.Close()
				g.srtSock = nil
			}
		}
		g.mu.Unlock()

		if keep {
			newGroups = append(newGroups, g)
		} else {
			log.Printf("[group %p] removed (no connections)", g)
		}
	}
	groups = newGroups
}

// srt_handshake_t layout (64 bytes total):
//
//	Offset  0: srt_header_t (16 bytes)
//	  [0:2]   type          = 0x8000 (handshake)
//	  [2:4]   subtype
//	  [4:8]   info
//	  [8:12]  timestamp
//	  [12:16] dest_id
//	Offset 16: version       (4 bytes)
//	Offset 20: enc_field     (2 bytes)
//	Offset 22: ext_field     (2 bytes)
//	Offset 24: initial_seq   (4 bytes)
//	Offset 28: mtu           (4 bytes)
//	Offset 32: mfw           (4 bytes)
//	Offset 36: handshake_type(4 bytes)
//	Offset 40: source_id     (4 bytes)
//	Offset 44: syn_cookie    (4 bytes)
//	Offset 48: peer_ip       (16 bytes)
//	Total: 64 bytes
const srtHandshakeLen = 64

func resolveSRTAddr(host string, port uint16) (*net.UDPAddr, error) {
	addrs, err := net.LookupIP(host)
	if err != nil {
		return nil, err
	}

	hsPkt := make([]byte, srtHandshakeLen)
	binary.BigEndian.PutUint16(hsPkt[0:], SRTTypeHandshake) // header.type
	binary.BigEndian.PutUint32(hsPkt[16:], 4)               // version
	binary.BigEndian.PutUint16(hsPkt[22:], 2)               // ext_field
	binary.BigEndian.PutUint32(hsPkt[36:], 1)               // handshake_type = induction

	for _, ip := range addrs {
		raddr := &net.UDPAddr{IP: ip, Port: int(port)}
		conn, err := net.DialUDP("udp", nil, raddr)
		if err != nil {
			continue
		}
		conn.SetDeadline(time.Now().Add(2 * time.Second))
		_, err = conn.Write(hsPkt)
		if err == nil {
			buf := make([]byte, MTU)
			n, err := conn.Read(buf)
			if err == nil && n == srtHandshakeLen {
				conn.Close()
				return raddr, nil
			}
		}
		conn.Close()
	}
	if len(addrs) == 0 {
		return nil, fmt.Errorf("no IPs for host %s", host)
	}
	return &net.UDPAddr{IP: addrs[0], Port: int(port)}, nil
}

func removeGroup(g *Group) {
	groupsMu.Lock()
	defer groupsMu.Unlock()
	for i, gg := range groups {
		if gg == g {
			groups = append(groups[:i], groups[i+1:]...)
			break
		}
	}
	g.mu.Lock()
	if g.srtSock != nil {
		g.srtSock.Close()
		g.srtSock = nil
	}
	g.mu.Unlock()
}

func main() {
	var (
		srtlaPort = flag.Uint("srtla_port", 5000, "UDP port to listen on for SRTLA")
		srtHost   = flag.String("srt_hostname", "127.0.0.1", "Downstream SRT server host")
		srtPort   = flag.Uint("srt_port", 5001, "Downstream SRT server port")
		verbose   = flag.Bool("verbose", false, "Enable verbose logging")
	)
	flag.Parse()

	if *verbose {
		log.SetFlags(log.LstdFlags | log.Lshortfile)
	} else {
		log.SetFlags(0)
	}

	var err error
	srtAddr, err = resolveSRTAddr(*srtHost, uint16(*srtPort))
	if err != nil {
		log.Fatalf("could not resolve downstream SRT server: %v", err)
	}
	log.Printf("downstream SRT server %s", srtAddr)

	laddr := &net.UDPAddr{IP: net.IPv6unspecified, Port: int(*srtlaPort)}
	srtlaSock, err = net.ListenUDP("udp", laddr)
	if err != nil {
		log.Fatalf("failed to listen on UDP port %d: %v", *srtlaPort, err)
	}
	_ = srtlaSock.SetReadBuffer(RecvBufSize)
	_ = srtlaSock.SetWriteBuffer(SendBufSize)

	log.Printf("listening on %s", srtlaSock.LocalAddr())

	go func() {
		buf := make([]byte, MTU)
		for {
			n, addr, err := srtlaSock.ReadFromUDP(buf)
			if err != nil {
				log.Printf("read error: %v", err)
				continue
			}
			pkt := make([]byte, n)
			copy(pkt, buf[:n])
			handleSRTLAIncoming(pkt, addr)
		}
	}()

	ticker := time.NewTicker(CleanupPeriod)
	for range ticker.C {
		cleanup()
	}
}
