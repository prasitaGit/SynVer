````markdown

SYNVER is a synthesizer for C programs that is backed by a **fully verified C compiler** and a **Rocq (Coq)** proof certifying the correctness of the generated program with respect to its specification.

At present, SYNVER has verified support for the following data structures:
- **Arrays**
- **Singly Linked Lists**
- **Binary Search Trees**

The corresponding verified proofs can be found in:
- `sllProof.v`
- `bstFunctionalProofs.v`

--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

## 🧩 Requirements

Please ensure the following dependencies are installed before running SYNVER:

- [Coq 8.19.2](https://coq.inria.fr/)
- [VST (Verified Software Toolchain) 2.14](https://vst.cs.princeton.edu/)
- [CompCert](https://compcert.org/)
- [OpenAI Python Client](https://github.com/openai/openai-python)
- `python3`
- A valid **OpenAI API key**

--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

## ⚙️ Running Benchmarks

To build and run SYNVER’s benchmarks, execute the following commands:

```bash
make clean
make
python3 synthesize.py <API-KEY>
````

This process:

* Calls all specifications under the `specText/` directory.
* Uses **GPT-5-mini** as both the *coder LLM* (for code synthesis) and *prover LLM* (for proof generation).

You can modify the LLM versions manually inside:

* `synthesize.py` → for the coder LLM
* `genProof.py` → for the prover LLM

---

## Custom Benchmarks

You can curate your own benchmarks as follows:

1. Create an **input prompt file** following the format of files under `specText/`.
2. Create a **specification file** following the format of files under `proof/`.

You can:

* **Hard-code** the prompt and specification file names inside `synthesize.py` or `genProof.py`, **or**
* Create your own directories (e.g., `mySpecs/`, `myProofs/`) and update the directory paths in those scripts.

---

## 🐳 Docker Support

You can also try SYNVER using a pre-built Docker image with all dependencies pre-installed:

🔗 [Zenodo Record (Docker Image)](https://zenodo.org/records/17230953)

Alternatively, you can build the image yourself using the provided `Dockerfile` in this repository.

---

## 🧾 Citation

If you use **SYNVER** in your research, please cite our Zenodo DOI above.

---

## 🧾 Pre-print

🔗 [Paper](https://prasitagit.github.io/papers/SynverPreprint.pdf)

---

## 📜 License

This repository is released under an open-source license. Please see the `LICENSE` file for details.

