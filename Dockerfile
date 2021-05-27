FROM gcc:latest
RUN apt update && apt -y install cmake
RUN git clone https://github.com/vprover/vampire
WORKDIR /vampire
RUN git submodule update --init z3
WORKDIR /vampire/z3/build
RUN cmake .. -DZ3_SINGLE_THREADED=ON
RUN make -j8
WORKDIR /vampire/build
RUN cmake ..
RUN make -j8
RUN mv bin/vampire_z3_rel_* ../vampire