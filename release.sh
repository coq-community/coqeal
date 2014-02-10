#!/bin/bash

echo "Script name: $0"
if [ $# -ne 1 ];
    then echo "tag expected as argument."; exit 1
fi

VERSION=$1
ROOT=$(git rev-parse --show-toplevel)
TMP=$(mktemp -d)
git clone $ROOT $TMP/CoqEAL

cd $TMP/CoqEAL/theory
make dist

cd $TMP/CoqEAL/refinements
make dist

mkdir -p $ROOT/release
cd $ROOT/release
mv $TMP/CoqEAL/theory/CoqEAL_theory.tgz           CoqEAL_theory.$VERSION.tgz
mv $TMP/CoqEAL/refinements/CoqEAL_refinements.tgz CoqEAL_refinements.$VERSION.tgz
md5sum CoqEAL_theory.$VERSION.tgz      > CoqEAL_theory.$VERSION.md5
md5sum CoqEAL_refinements.$VERSION.tgz > CoqEAL_refinements.$VERSION.md5
