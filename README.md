# algorithm-correction-FOL

## Getting Started

These instructions will help you set up the environment and build the project on your local machine. 

**Note:** The following installation guide is tailored for **Ubuntu/Debian-based** Linux distributions.

### 1. Install System Dependencies
First, update your package lists and install the required system tools: `opam` (OCaml package manager), `make` (build automation tool), a full LaTeX distribution (for documentation), and a PDF viewer (`evince`).

```bash
sudo apt update
sudo apt install opam make texlive-full evince
```

### 2. Initialize the Environment
Initialize `opam` and update your current terminal environment variables to ensure the installed tools are recognized.

```bash
opam init
eval $(opam env)
```

### 3. Install The Rocq Prover
Install the core proof assistant ecosystem.

```bash
opam install rocq-prover
```

You can verify the installation by checking the version: 

> (Note: This project was built and tested using The Rocq Prover, version 9.2 compiled with OCaml 4.14.1)


```bash
rocq --version
```

### 4. Build the Project
Once all dependencies are installed and the environment is active, navigate to the project root and run the default build command to compile the source files.

```bash
make
```