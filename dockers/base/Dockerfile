################### Build Vampire 
FROM satcomp-common-base-image
USER root
#  Install required softwares
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt install -y cmake g++

#  Build Vampire
WORKDIR /home
RUN git clone https://github.com/vprover/vampire --branch smtcomp23 --single-branch
WORKDIR /home/vampire
RUN git submodule update --init z3
WORKDIR /home/vampire/z3/build
RUN cmake .. -DZ3_SINGLE_THREADED=TRUE -DZ3_BUILD_LIBZ3_SHARED=FALSE 
RUN make -j4
WORKDIR /home/vampire/build
RUN cmake .. -DBUILD_SHARED_LIBS=0 
RUN make -j4
RUN mv bin/vampire_z3_rel_* bin/vampire
