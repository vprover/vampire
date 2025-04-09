FROM debian:12.10 AS builder
USER root

#  Install required software
RUN apt-get update
RUN DEBIAN_FRONTEND=noninteractive apt install -y git cmake clang

#  Build Vampire
WORKDIR /home
ARG branch=master

# Check out Vampire
RUN git clone https://github.com/vprover/vampire --branch $branch --single-branch

# Check out submodules
WORKDIR /home/vampire
RUN git submodule update --init --depth=1

# Build Z3
WORKDIR /home/vampire/z3/build
RUN cmake .. -DZ3_SINGLE_THREADED=TRUE -DZ3_BUILD_LIBZ3_SHARED=FALSE
RUN make -j4

# Build Vampire
WORKDIR /home/vampire/build
RUN cmake .. -DBUILD_SHARED_LIBS=0
RUN make -j4

# Create runner container
FROM alpine:3.21
COPY --from=builder /home/vampire/build/vampire ./
ENTRYPOINT [ "./vampire" ]
