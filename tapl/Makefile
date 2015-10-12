lhs2TeX -o STLC-writeup.tex STLC-writeup.lagda --agda
# replace unrecognized unicode chars
sed -i -e 's/ˢ/\\(^s\\)/g; s/ᵏ/\\(^k\\)/g' STLC-writeup.tex
pdflatex STLC-writeup.tex
