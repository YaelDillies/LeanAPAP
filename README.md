# Arithmetic Progressions - Almost Periodicity

[![.github/workflows/push.yml](https://github.com/YaelDillies/LeanAPAP/actions/workflows/push.yml/badge.svg)](https://github.com/YaelDillies/LeanAPAP/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/YaelDillies/LeanAPAP)

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements
and theorem proofs. Digitisation, or formalisation, is a process where the source material,
typically a mathematical textbook or a pdf file or website or video, is transformed into definitions
in a target system consisting of a computer implementation of a logical theory (such as set theory
or type theory).

## The source

The definitions, theorems and proofs in this repository are taken from the exposition of Bloom and
Sisask on the Kelley-Meka bound on Roth numbers [2302.07211](https://arxiv.org/abs/2302.07211).

The main result is that there is some constant `c > 0` such that, if `A ⊆ {1, ..., N}` contains no
non-trivial arithmetic progression of length 3, then `|A| ≤ N/exp(c * (log n)^(1/12)))` for some
constant `c > 0`. This is an amazing improvement over previous bounds, which were all of the form
`N/(log n)^c` for some constant `c`.

## The target

The formal system which we are using as a target system is Lean's dependent type theory. Lean is a
project being developed at AWS and Microsoft Research by Leonardo de Moura and his team.

At this stage, mathlib4 contains all the background material that we need. However, not all
quality-of-life improvements that we know from Lean 3 have made it to Lean 4 (yet) and Lean 4
suffers from its own problems that currently make it unsuitable for new formalisation of
research-level mathematics. As a consequence, we are sticking to Lean 3 until the project is
complete. Then we will port it to Lean 4 in order to upstream our basic results.

## Content of this project

This project currently contains about 3k lines of Lean code about the discrete (difference)
convolution, discrete Lp norms, discrete Fourier transform. It also contains proofs of a version of
almost periodicity and of a quantitative version of the Marcinkiewicz-Zygmund inequality.

Once finished, this project will contain two main results (here `R` is the Roth number, the maximum
size of a set without three term arithmetic progressions):
* The **finite field case**: A proof that `R(F_q^n) ≤ q ^ (n - c * n ^ (1/9))` for some constant
  `c`. This is worse than the Ellenberg-Gijswijt bound `R(F_q^n) ≤ q ^ (n - c * n)` which was
  formalised in [Dahmen, Hölzl, Lewis](https://drops.dagstuhl.de/opus/volltexte/2019/11070/). The
  goal here is therefore not to improve on the existing bound but instead demonstrate the
  probability and Fourier analysis techniques, whereas Ellenberg-Gijswijt used the polynomial
  method.
* The **integer case**: A proof that `R(n) ≤ N/exp(c * (log n)^(1/9)))`, using the same techniques
  as in the finite field case, except for the fact that we now use Bohr sets instead of subspaces.
  This bound is a slight improvement over the Kelley-Meka bound (with `1/12` as the exponent instead
  of `1/9`). It is due to Bloom and Sisask.

### Code organisation

The Lean code is contained in the directory `src/`. The subdirectories are:
* `mathlib`: Material missing from existing mathlib developments
* `prereqs`: New developments to be integrated to mathlib
* `physics`: The physical (as opposed to Fourier space) proof steps that are shared
  between the finite field cases and integer case
* `finite_field`: The proof steps specific to the finite field case
* `integer`: The proof steps specific to the integer case

See the next section for how to browse it.

### What next?

Almost periodicity is nowadays a standard tool in additive combinatorics. The version we formalised
is sufficient for many applications. In particular, it gives one of the best known bounds on
Freiman's theorem. If some time is left at the end of the project, we might tackle Freiman's
theorem.

The discrete convolution/Lp norm/Fourier transform material belongs in mathlib and we hope to PR it
there once the transition to Lean 4 has completed. Almost periodicity should similarly be upstreamed
to mathlib given the numerous applications. The rest of the material might forever live in this
repository.

## How to browse this repository

### Blueprint

Below we explain how to engage with the Lean code directly.
We also provide a [blueprint](https://YaelDillies.github.io/LeanAPAP/)
including a [dependency graph](https://YaelDillies.github.io/LeanAPAP/blueprint/dep_graph_document.html)
of the main ingredients in the repository.
This blueprint is developed in sync with the Lean formalization,
and will hence see frequent updates during the length of the project.
More information on building the blueprint locally is given below.

### Getting the project

At the moment, the recommended way of browsing this repository,
is by using a Lean development environment.
Crucially, this will allow you to introspect Lean's "Goal state" during proofs,
and easily jump to definitions or otherwise follow paths through the code.

We are looking into ways to setup an online interactive website
that will provide the same experience without the hassle of installing a complete
Lean development environment.

For the time being: please use the
[installation instructions](https://leanprover-community.github.io/get_started.html#regular-install)
to install Lean and a supporting toolchain.
After that, download and open a copy of the repository
by executing the following command in a terminal:
```
leanproject get YaelDillies/LeanAPAP
code LeanAPAP
```
For detailed instructions on how to work with Lean projects,
see [this](https://leanprover-community.github.io/install/project.html). The script
`scripts/get-cache.sh` in the folder `LeanAPAP` will download the `olean` files created by our
continuous integration. This will save you some time by not having to run `leanproject build`.

### Reading the project

With the project opened in VScode,
you are all set to start exploring the code.
There are two pieces of functionality that help a lot when browsing through Lean code:

* "Go to definition": If you right-click on a name of a definition or lemma (such as `dconv` or
  `Lpnorm`), then you can choose "Go to definition" from the menu, and you will be taken to the
  relevant location in the source files. This also works by `Ctrl`-clicking on the name.
* "Goal view": in the event that you would like to read a *proof*, you can step through the proof
  line-by-line, and see the internals of Lean's "brain" in the Goal window. If the Goal window is
  not open, you can open it by clicking on one of the icons in the top right hand corner.

### Building the blueprint locally

To build the web version of the blueprint locally, you need a working LaTeX installation.
Furthermore, you need some dependencies.  Under Linux, you should be able to get the prepackaged
ones with something like:
```
sudo apt install graphviz libgraphviz-dev libjpeg-dev pandoc
pip3 install invoke
```

Under Mac OS, you should be able to get these with:
```
brew install graphviz pandoc
pip3 install pygraphviz invoke
```
([This stackoverflow answer](https://stackoverflow.com/a/70439868/) may help to fix an error
installing `pygraphviz`.

A couple of dependencies must be installed from source, for now (`leanblueprint` is not yet
released, and the released `plastex` is out of date):
```
cd .. # go to a folder where you are happy to clone git repos
git clone https://github.com/plastex/plastex
pip3 install ./plastex
git clone https://github.com/PatrickMassot/leanblueprint
pip3 install ./leanblueprint
```

To actually build the blueprint, `cd` to the `LeanAPAP` folder and run
```
leanproject get-mathlib-cache
leanproject build
inv all html
```

To view the web version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.


## Acknowledgements

Our project builds on mathlib. We must therefore thank its numerous contributors without whom this
project couldn't even have started.

Much of the project infrastructure has been adapted from
* [sphere eversion](https://leanprover-community.github.io/sphere-eversion/)
* [liquid tensor experiment](https://github.com/leanprover-community/liquid/)
* [unit fractions](https://github.com/b-mehta/unit-fractions/)

## Source reference

`[BS]` : https://arxiv.org/abs/2302.07211

[BS]: https://arxiv.org/abs/2302.07211
