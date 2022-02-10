build:
	$(CXX) -std=c++14 main.cpp -o logos

debug:
	$(CXX) -std=c++14 -g main.cpp -o logos

install: build
	cp logos /bin/

uninstall:
	rm /bin/logos
