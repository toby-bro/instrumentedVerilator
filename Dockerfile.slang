FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    build-essential \
    cmake \
    gcc \
    git \
    lcov \
    python3 \
    python3-pip \
    python3-setuptools \
    python3-wheel \
    libboost-all-dev \
    vim && rm -rf /var/lib/apt/lists/*

RUN pip3 install git+https://github.com/RPGillespie6/fastcov.git --break-system-packages

RUN git clone --depth 1 https://github.com/MikePopoloski/slang.git /slang

WORKDIR /slang

RUN sed -i 's/SLANG_INCLUDE_COVERAGE "Enable code coverage" OFF/SLANG_INCLUDE_COVERAGE "Enable code coverage" ON/' CMakeLists.txt
RUN cmake -B build -DCMAKE_BUILD_TYPE=Debug -DCMAKE_CXX_FLAGS="--coverage" -DCMAKE_EXE_LINKER_FLAGS="--coverage"  
RUN cmake --build build -j`nproc`
ENV PATH="/slang/build/bin:${PATH}"
