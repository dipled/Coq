# Coq
Alguns capítulos do Logical Foundations resolvidos

## Como compilar os arquivos:
- crie um arquivo chamado _CoqProject e escreva o seguinte dentro dele :
  -R . [NomeDoProjeto]
  ./[NomeDoArquivo].v

- execute o comando coq_makefile -f _CoqProject -o CoqMakeFile
- compile com make -f Coqmakefile
- depois, podemos limpar com make -f Coqmakefile clean
