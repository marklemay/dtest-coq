FROM coqorg/coq:latest

RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam repository add coq-released --all-switches
RUN opam install coq-mathcomp-ssreflect

COPY --chown=coq . /dtest-coq

WORKDIR /dtest-coq

RUN make all

