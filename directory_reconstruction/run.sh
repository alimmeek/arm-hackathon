#!/bin/sh
#cat input.txt | ./target/debug/directory_reconstruction
hyperfine --warmup 3 "cat input.txt| ./target/release/directory_reconstruction"