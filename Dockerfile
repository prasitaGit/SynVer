# Start from Debian slim with OCaml and OPAM
FROM debian:bookworm-slim

# Set noninteractive mode for apt
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    m4 \
    opam \
    git \
    curl \
    wget \
    unzip \
    pkg-config \
    zlib1g-dev \
    python3 \
    python3-pip \
    python3-setuptools \
    python3-venv \
    ca-certificates \
    vim \
    libgmp-dev \
    libcoq-ocaml-dev \
    && rm -rf /var/lib/apt/lists/*

# Install Python packages (OpenAI client + Alectryon)
#RUN pip3 install --no-cache-dir openai alectryon
RUN pip3 install --no-cache-dir --break-system-packages openai alectryon

# Initialize OPAM and set OCaml version
RUN opam init -y --disable-sandboxing && \
    opam switch create 4.14.2 && \
    opam switch set 4.14.2 && \
    eval $(opam env)

# Install Coq 8.19.2
RUN opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam install -y coq.8.19.2

# Install SerAPI (needed for Alectryon)
RUN opam pin add coq-serapi 8.19.0+0.19.3 --yes && \
    opam install -y coq-serapi


# Install VST 2.14 (via opam)
RUN opam install -y coq-vst.2.14

# Install CompCert 3.13.1 (requires license acceptance)
RUN opam install -y coq-compcert.3.13.1

# Persist OPAM environment
SHELL ["/bin/bash", "-c"]
RUN echo 'eval $(opam env)' >> /etc/bash.bashrc

# Set default working directory
WORKDIR /
RUN git clone https://github.com/prasitaGit/SynVer.git --depth 1
WORKDIR /SynVer

# Default command
CMD ["/bin/bash"]
