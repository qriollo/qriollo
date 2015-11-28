.PHONY : qr clean

qr :
	ghc -isrc --make src/Main.hs -o qr -rtsopts

clean :
	rm -rf src/*.o src/*.hi
	rm -rf src/Backend/*.o src/Backend/*.hi

