#!/bin/bash -e
make check
pushd expressions && make check && popd
pushd deep-expressions && make check && popd
