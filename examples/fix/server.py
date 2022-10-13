
import socket
s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
s.bind(("",4997))
s.listen(1)
conn, addr = s.accept()

buf = ""

print('Connected by', addr)
while True:
    data = conn.recv(1024)
    if not data:
        break
    print data
    conn.sendall("pong\n")
    
