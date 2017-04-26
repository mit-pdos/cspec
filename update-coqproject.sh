#!/bin/bash

rm -f _CoqProject

echo "-R . Pocs" >> _CoqProject
git ls-files "*.v" >> _CoqProject
