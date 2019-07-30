FROM fedora

WORKDIR /opt

RUN dnf update -y && \
        dnf install -y gcc-c++ libstdc++-static glibc-static gmp-static cmake make git zlib-devel gmp-devel

RUN cd /opt && \
        git clone https://github.com/Z3Prover/z3.git && \
        mkdir z3/build && \
        cd z3/build && \
        cmake -DBUILD_LIBZ3_SHARED=false -DCMAKE_INSTALL_PREFIX=/opt/z3 -G "Unix Makefiles" .. && \
        make -j8 && \
        make install

RUN cd /opt/ && \
        git clone https://github.com/vprover/vampire.git && \
        mkdir vampire/build && \
        cd vampire && \
        git checkout cmake && \
        cd build && \
        cmake -DBUILD_SHARED_LIBS=0 -DCMAKE_INSTALL_PREFIX=/opt/vampire -DZ3_DIR=/opt/z3/lib64/cmake/z3 -G "Unix Makefiles" .. && \
        make -j8

RUN cp -r /opt/vampire/build/bin /artifacts/
RUN /opt/vampire/build/bin/vampire --help
