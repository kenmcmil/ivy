#!/bin/sh

mkdir -R ~/.vim/syntax
cp ivy.vim ~/.vim/syntax

mkdir -R ~/.vim/ftdetect
echo "au BufRead,BufNewFile *.ivy set filetype=ivy" >> ~/.vim/ftdetect
