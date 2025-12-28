#!/bin/bash

# Exit on error
set -e

echo "🚀 Starting Build Pipeline..."

# 1. Compile Agda to LaTeX
echo "📦 Compiling Agda to LaTeX..."
agda --safe --without-K --latex FirstDistinction.lagda.tex

# 2. Build PDF
echo "📄 Building PDF..."
cd latex

# Use xelatex for better Unicode support if available, otherwise pdflatex
if command -v xelatex &> /dev/null; then
    COMPILER="xelatex"
else
    COMPILER="pdflatex"
fi

echo "Using compiler: $COMPILER"

# Run twice for references/toc
$COMPILER -interaction=nonstopmode FirstDistinction.tex > /dev/null
$COMPILER -interaction=nonstopmode FirstDistinction.tex > build.log

# 3. Move PDF to root
mv FirstDistinction.pdf ../FirstDistinction.pdf
cd ..

echo "✅ Build Complete: FirstDistinction.pdf"
