#!/usr/bin/env sh

VERSION=1.4.0

cat << END > version.ml

let version = "$VERSION"
let build_date = "$(date)"

END

