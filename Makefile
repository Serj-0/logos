build:
	g++ -std=c++14 main.cpp -o logos

install: build
	cp logos /bin/

uninstall:
	rm /bin/logos
