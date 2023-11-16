ROOT    := ../..
VS      := $(wildcard *.v) $(wildcard BTree/*.v)
VS      := $(filter-out Extract.v, $(VS))

R       := -R $(ROOT)/src/coq Ynot \
           -R $(ROOT)/examples/Data Data \
           -R $(ROOT)/examples/Parse Parse \
           -R . Rdb

include ../Makefile.ynot