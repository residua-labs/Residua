package main

import (
	"bufio"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"net"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/knusbaum/go9p"
	"github.com/knusbaum/go9p/fs"
	"github.com/knusbaum/go9p/proto"
)

const frameCap = 8192

func fileServer() (go9p.Srv, error) {
	const owner = "fixture"
	files, root := fs.NewFS(owner, owner, 0777,
		fs.IgnorePermissions(),
		fs.WithCreateFile(fs.CreateStaticFile),
		fs.WithCreateDir(fs.CreateStaticDir),
		fs.WithRemoveFile(fs.RMFile))
	mount := fs.NewStaticDir(files.NewStat("fs", owner, owner, 0777|proto.DMDIR))
	dir := fs.NewStaticDir(files.NewStat("root", owner, owner, 0777|proto.DMDIR))
	file := fs.NewStaticFile(files.NewStat("file", owner, owner, 0666), []byte("A"))
	for _, edge := range []struct {
		dir   *fs.StaticDir
		child fs.FSNode
	}{{root, mount}, {mount, dir}, {dir, file}} {
		if err := edge.dir.AddChild(edge.child); err != nil {
			return nil, err
		}
	}
	return files.Server(), nil
}

func connect() (net.Conn, error) {
	server, err := fileServer()
	if err != nil {
		return nil, err
	}
	client, peer := net.Pipe()
	go func() {
		defer peer.Close()
		_ = go9p.ServeReadWriter(peer, peer, server)
	}()
	return client, nil
}

func exchange(conn net.Conn, request []byte) ([]byte, error) {
	if err := conn.SetDeadline(time.Now().Add(time.Second)); err != nil {
		return nil, err
	}
	if _, err := conn.Write(request); err != nil {
		return nil, err
	}
	var header [4]byte
	if _, err := io.ReadFull(conn, header[:]); err != nil {
		return nil, err
	}
	size := binary.LittleEndian.Uint32(header[:])
	if size < 7 || size > frameCap {
		return nil, fmt.Errorf("response header declares size %d", size)
	}
	response := make([]byte, size)
	copy(response, header[:])
	_, err := io.ReadFull(conn, response[4:])
	return response, err
}

func collect(input io.Reader, output io.Writer) error {
	scanner := bufio.NewScanner(input)
	var connection net.Conn
	defer func() {
		if connection != nil {
			connection.Close()
		}
	}()
	seen := make(map[string]bool)
	var current string
	var previous int
	for scanner.Scan() {
		fields := strings.Split(scanner.Text(), "\t")
		if len(fields) != 3 || fields[0] == "" {
			return fmt.Errorf("expected session, ordinal, request")
		}
		session := fields[0]
		ordinal, err := strconv.Atoi(fields[1])
		if err != nil {
			return err
		}
		if session != current {
			if seen[session] {
				return fmt.Errorf("repeated session %s", session)
			}
			seen[session] = true
			if connection != nil {
				connection.Close()
			}
			connection, err = connect()
			if err != nil {
				return err
			}
			current, previous = session, 0
		}
		if ordinal != previous+1 {
			return fmt.Errorf("nonconsecutive ordinal in %s: %d", session, ordinal)
		}
		request, err := hex.DecodeString(fields[2])
		if err != nil || len(request) < 7 || len(request) > frameCap ||
			int(binary.LittleEndian.Uint32(request[:4])) != len(request) {
			return fmt.Errorf("malformed request in %s row %d", session, ordinal)
		}
		response, err := exchange(connection, request)
		if err != nil {
			return fmt.Errorf("%s row %d: %w", session, ordinal, err)
		}
		if _, err := fmt.Fprintf(output, "%s\t%d\t%x\t%x\n", session, ordinal, request, response); err != nil {
			return err
		}
		previous = ordinal
	}
	if err := scanner.Err(); err != nil {
		return err
	}
	if len(seen) == 0 {
		return fmt.Errorf("no sessions")
	}
	return nil
}

func main() {
	if err := collect(os.Stdin, os.Stdout); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
