#! /bin/bash

./prepare_archive.sh
cp -f artifact.zip vagrant/
(cd vagrant; vagrant up)
# (cd vagrant; vagrant reload --provision)
