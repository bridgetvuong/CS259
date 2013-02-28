#
# CS259 Final Project
#
# This is a Makefile for the Murphi model of the PE3WAKA protocol.
#

MURPHI = ./cmurphi5.4.4/src/mu 
MOPTS  = 

CXX = g++ -DCATCH_DIV -fno-default-inline -Wno-deprecated
INCLUDE = ./cmurphi5.4.4/include/

pe3waka: pe3waka.cpp
	${CXX} -I${INCLUDE} pe3waka.cpp -o pe3waka -lm

pe3waka.cpp: pe3waka.m
	${MURPHI} ${MOPTS} pe3waka.m

clean:
	rm -f pe3waka pe3waka.cpp

