#! /bin/bash

proofs=$(find src -name '*.v')
vagrant_files="vagrant/Vagrantfile vagrant/pg_config/emacs_config vagrant/pg_config/install_packages.el vagrant/pg_config/setup_emacs.sh"
top_files="configure Makefile README.md LICENSE.md print_axioms.sh"

rm artifact.zip || true
zip artifact $proofs $vagrant_files $top_files
