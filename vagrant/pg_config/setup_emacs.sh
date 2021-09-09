rm ~/.emacs
cp emacs_config ~/.emacs
# echo "y" is to to answer emacs prompt; didn't find a way to avoid it at all
# two scripts are needed: emacs config and the installation script itself
echo "y" | emacs -batch -l ~/.emacs -l install_packages.el
