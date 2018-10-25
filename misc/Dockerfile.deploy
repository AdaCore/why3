FROM bench-image-system-stable

USER root

RUN adduser --disabled-password --gecos '' guest

USER why3

COPY --chown=why3:why3 . why3
WORKDIR /home/why3/why3

RUN eval `opam config env` && \
    ./configure && \
    make

USER root

RUN make install

USER guest
ENV HOME /home/guest
WORKDIR /home/guest

RUN why3 config --detect
