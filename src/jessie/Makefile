
FRAMAC_SHARE    :=$(shell frama-c -print-path)
FRAMAC_LIBDIR   :=$(shell frama-c -print-libpath)
PLUGIN_NAME     := Jessie3
PLUGIN_CMO      := ACSLtoWhy3 register

SHELL := /bin/bash

PLUGIN_EXTRA_BYTE:= /usr/lib/ocaml/why3/why3.cma 
PLUGIN_EXTRA_OPT:= /usr/lib/ocaml/why3/why3.cmxa
PLUGIN_BFLAGS:= -I +why3 
PLUGIN_OFLAGS:= -I +why3 
PLUGIN_LINK_BFLAGS:= -I +why3 
PLUGIN_LINK_OFLAGS:= -I +why3 
PLUGIN_TESTS_DIRS := basic

include $(FRAMAC_SHARE)/Makefile.dynamic

tests::
	grep Status tests/basic/result/*

