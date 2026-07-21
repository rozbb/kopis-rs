#!/bin/bash

set -eux

/home/dev/aeneas/charon/bin/charon cargo --preset=aeneas
/home/dev/aeneas/bin/aeneas kopis_kem.llbc -backend lean -loops-to-rec
rm kopis_kem.llbc
