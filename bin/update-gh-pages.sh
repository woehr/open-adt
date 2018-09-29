#! /usr/bin/env nix-shell
#! nix-shell -i bash -p stack

set -e

stack haddock
git checkout gh-pages
# stack leaves things in these directories, so they stick around.
rm -rf open-adt/.stack-work open-adt-tutorial/.stack-work
rmdir open-adt open-adt-tutorial
git rm -r ./*
cp -r .stack-work/install/x86_64-linux-nix/lts-12.9/8.4.3/doc/* .
git add .
echo "Verify changes before committing and pushing. :)"
echo "And remember you are on the gh-pages branch now."
