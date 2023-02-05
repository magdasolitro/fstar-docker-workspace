FROM fstarlang/fstar:latest
RUN echo 'export PATH="$PATH:/home/build/FStar/bin"' >> /home/build/.bashrc
WORKDIR /workspace