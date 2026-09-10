#/bin/sh

cd examples

for i in *.v
do
  coqdoc -s --no-lib-name -parse-comments --no-index --utf8 --interpolate --html \
      --external http://github.com/rocq-prover/equations/tree/master Equations \
      -Q ../theories Equations -R . Examples -d ../docs/examples $i
done

cd ..

git checkout docs/examples/coqdoc.css
