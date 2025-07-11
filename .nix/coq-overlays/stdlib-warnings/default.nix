{ stdlib }: stdlib.overrideAttrs {
  preConfigure = ''
    echo "-arg -w -arg +default" > theories/_CoqProject.tmp
    cat theories/_CoqProject >> theories/_CoqProject.tmp
    mv theories/_CoqProject.tmp theories/_CoqProject
  '';
}
