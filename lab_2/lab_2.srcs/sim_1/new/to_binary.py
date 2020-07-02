code = '200200052003000c2067fff700e220250064282400a4282010a7000a0064202a108000012005000000e2202a0085382000e23822ac6700448C0200500800001120020001ac020054'

char2num = {'a':10, 'b':11, 'c':12, 'd':13, 'e':14, 'f':15}
for i in range(10):
    char2num[str(i)] = i

filename = 'memfile.dat'
file = open(filename, 'wb')
for i in range(len(code)//2):
    file.write(( char2num[code[i]]*16 + char2num[code[i+1]] ).to_bytes(length=1, byteorder='big'))
file.close()
