#------------------------------------------------------------
#----To build: docker build -t vampire:mtpa-gnn-2026 .

FROM ubuntu:22.04

#----Install build dependencies
RUN apt-get update \
    && apt-get install -y --no-install-recommends git cmake make g++ wget unzip ca-certificates python3 \
    && update-ca-certificates \
    && rm -rf /var/lib/apt/lists/*

#----Create artifacts directory
RUN mkdir -p /artifacts

#----Download libtorch (Linux x86_64, cxx11 ABI, CPU)
RUN wget -q https://download.pytorch.org/libtorch/cpu/libtorch-shared-with-deps-2.10.0%2Bcpu.zip -O /tmp/libtorch.zip \
    && unzip -q /tmp/libtorch.zip -d / \
    && rm /tmp/libtorch.zip
ENV LIBTORCH=/libtorch

#----Clone repository
RUN git clone --branch mtpa-gnn-2026 --depth 1 --recurse-submodules --shallow-submodules https://github.com/vprover/vampire.git
WORKDIR /vampire

#----Build Z3
RUN mkdir -p z3/build \
     && cd z3/build \
     && cmake .. -DZ3_BUILD_LIBZ3_SHARED=FALSE -DZ3_SINGLE_THREADED=1 -DCMAKE_BUILD_TYPE=Release \
     && make -j$(nproc)

#----Build cadical
RUN cd cadical && ./configure && make -j$(nproc)

#----Build Vampire
RUN make vampire_z3_rel -j$(nproc) \
   && cp vampire_z3_rel_* /artifacts/vampire

# RUN make vampire_rel -j 5 \
#     && cp vampire_rel_* /artifacts/vampire

#----Build Vampire - HO
RUN git clone --branch hol --depth 1 --recurse-submodules --shallow-submodules https://github.com/vprover/vampire.git /vampire-ho
RUN mkdir -p /vampire-ho/build \
     && cd /vampire-ho/build \
     && cmake /vampire-ho -DCMAKE_BUILD_TYPE=Release -DCMAKE_BUILD_HOL=ON -DCMAKE_DISABLE_FIND_PACKAGE_Z3=ON \
     && make vampire -j$(nproc) \
     && cp /vampire-ho/build/bin/vampire* /artifacts/vampire-ho \
     && rm -rf /vampire-ho

#----Add run_system script
ADD run_system /artifacts/

#------------------------------------------------------------
