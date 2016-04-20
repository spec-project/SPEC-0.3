
all: src/Makefile
	make -C src bedwyr spec

spec: src/Makefile
	make -C src spec

bedwyr: src/Makefile
	make -C src bedwyr

src/Makefile: src/Makefile.in configure
	./configure
configure: configure.ac
	autoconf

clean:
	make -C src clean

