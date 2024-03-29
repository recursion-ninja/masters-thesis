# Masters Thesis of [Alex Washburn][Personal-Site]


## Hunter College in the City of New York


# Project Overview


## Top level layout

The root directory of the project contains a few files which serve as very important resources (listed below).
Additionally, there are a number of directories and subdirectories which store the bulk of the project's code and resources.
Aside from the [`doc`][REPO-URI-doc] directory, which contains *very informative* project documentation, other subdirectories can be ignored by users wish to simply read or replicate the results of the project but not extend of modify it.
For those who are interested in extensiona and modification to the project, fully exploring the documentation directory ([`doc`][REPO-URI-doc]) will greatly inform and direct their understanding and manipulation of the other subdirectories included in the project.


### Important resources

| File                              | Description                  |
| :-------------------------------- | :--------------------------- |
| [`LICENSE`  ][REPO-URI-LICENSE]   | [MIT License][SPDX-MIT]      |
| [`Makefile` ][REPO-URI-Makefile]  | Build project components     |
| [`README.md`][REPO-URI-README.md] | Brief description of project |


#### [` LICENSE `][REPO-URI-LICENSE]:  
> The contents of this project are distributed under the open source [MIT License][SPDX-MIT].
> This license choice is based on the author's intent to broadly allow usage and extension while retaining a requirement of attribution.


#### [` Makefile `][REPO-URI-Makefile]:  
> The `Makefile` contains a number of commands for building the project.
> Functionality for building the project is decomposed into many make definition files located in [`src/mk`][REPO-URI-src-mk].
> This top-level `Makefile` contains the totality of make definitions within the project.
> Decomposition allows strategically constructing a smaller `Makefile` from a subset of the make definition files; a technique which is used by the author for constructing simple source bundles to be compiled and executed via [GNU Make][GNU-Make] on a remote computing cluster.
> 
> Verification is based on the CGKA security game played by an attacker parametwerized by `(T, C, N)` described in [Alwen et al][DOI-00].
> Without loss of generality the project assumes `T = C`, and hence the model verification must be parameterized by `(T, N)`.
> The `Makefile` is designed to accept these, along with other useful parameters.
>
> | Key      | Value                                                            |
> | :------- | :----------------------------------------------------------------|
> | `T`      | CGKA security parameter `T` (and implicitly `C`)                 |
> | `N`      | CGKA security parameter `N                                       |
> | `cores`  | Number of cores to use in multi-core environment                 |
> | `memory` | Pre-allocated and total RAM (in [Mebibytes][URI-WIKI-Binary-SI]) |
>
> **Example:**
> ```
> make installcheck T=6 N=8 cores=32 memory=262144
> ```
>
> The `Makefile` defines the following [GNU Make standard targets][GNU-Targets]:
>
> - `all`
> - `check`
> - `clean`
> - `distclean`
> - `dist`
> - `install`
> - `installcheck`
> - `installdirs`
> - `install-pdf`
> - `pdf`


#### [` README.md `][REPO-URI-README.md]:  
> Describes a brief description and motivation of the project.
> Directs the reader to documentation (including here) for more detailed project information.


### Project Subdivisions

The project has been arranged into multiple directories delineating different resources into related areas of interest.

| Directory               | Contents                               |
| :---------------------- | :------------------------------------- |
| [`bin` ][REPO-URI-bin ] | Compiled binary for model analysis     |
| [`data`][REPO-URI-data] | Read-only files for building project   |
| [`dist`][REPO-URI]      | Bundleds of parameterized source code  |
| [`doc` ][REPO-URI-doc ] | Plethora of useful project information |
| [`log` ][REPO-URI-log ] | Output logs of model verification      |
| [`src` ][REPO-URI-src ] | Source code for project components     |


### [`data`][REPO-URI-data] Project Components

| Sub-directory                           | Component                                 |
| :-------------------------------------- | :---------------------------------------- |
| [`data/make`   ][REPO-URI-data-make   ] | Decomposed `Make` definition files        |
| [`data/marshal`][REPO-URI-data-marshal] | Pre-computed model compilation parameters |
| [`data/pbs`    ][REPO-URI-data-pbs    ] | PBS template for cluster execution        |


### [`doc`][REPO-URI-doc] Project Components

| Sub-directory                             | Component                             |
| :---------------------------------------- | :------------------------------------ |
| [`doc/community`][REPO-URI-doc-community] | Community resources for contributions |


### [`log`][REPO-URI-log] Project Components

| Sub-directory                 | Component                                |
| :---------------------------- | :--------------------------------------- |
| [`log/records`][REPO-URI-log] | Recorded output of verifcation(s)        |
| [`log/trails` ][REPO-URI-log] | Counterexample(s) produced as Spin trail |


### [`src`][REPO-URI-src] Project Components

Within the [`src`][REPO-URI-src] directory there is a single sub-directory for each buildable project component.

| Sub-directory                       | Component                                    |
| :---------------------------------- | :------------------------------------------- |
| [`src/model` ][REPO-URI-src-model ] | CGKA model definition as Promela source      |
| [`src/slides`][REPO-URI-src-slides] | LaTeX and Markdown source for thesis defense |
| [`src/thesis`][REPO-URI-src-thesis] | LaTeX source for compiling the manuscript    |

[Personal-Site]:  https://recursion.ninja

[DOI-00]:         https://doi.org/10.1007/978-3-030-56784-2_9
[GNU-Make]:       https://www.gnu.org/software/make/
[GNU-Targets]:    https://www.gnu.org/software/make/manual/html_node/Standard-Targets.html#Standard-Targets
[SPDX-MIT]:       https://spdx.org/licenses/MIT.html
[WIKI-Binary-SI]: https://en.wikipedia.org/wiki/Binary_prefix

[REPO-URI              ]: https://github.com/recursion-ninja/masters-thesis
[REPO-URI-LICENSE      ]: https://github.com/recursion-ninja/masters-thesis/blob/master/doc/LICENSE
[REPO-URI-Makefile     ]: https://github.com/recursion-ninja/masters-thesis/blob/master/Makefile
[REPO-URI-README.md    ]: https://github.com/recursion-ninja/masters-thesis#readme
[REPO-URI-bin          ]: https://github.com/recursion-ninja/masters-thesis/tree/master/bin
[REPO-URI-data         ]: https://github.com/recursion-ninja/masters-thesis/tree/master/data
[REPO-URI-data-make    ]: https://github.com/recursion-ninja/masters-thesis/tree/master/data/make
[REPO-URI-data-marshal ]: https://github.com/recursion-ninja/masters-thesis/tree/master/data/marshalcy
[REPO-URI-data-pbs     ]: https://github.com/recursion-ninja/masters-thesis/tree/master/data/pbs
[REPO-URI-dist         ]: https://github.com/recursion-ninja/masters-thesis/tree/master/dist
[REPO-URI-doc          ]: https://github.com/recursion-ninja/masters-thesis/tree/master/doc
[REPO-URI-doc-community]: https://github.com/recursion-ninja/masters-thesis/tree/master/doc/community
[REPO-URI-doc-overview ]: https://github.com/recursion-ninja/masters-thesis/tree/master/doc/overview
[REPO-URI-log          ]: https://github.com/recursion-ninja/masters-thesis/tree/master/log
[REPO-URI-src          ]: https://github.com/recursion-ninja/masters-thesis/tree/master/src
[REPO-URI-src-model    ]: https://github.com/recursion-ninja/masters-thesis/tree/master/src/model
[REPO-URI-src-slides   ]: https://github.com/recursion-ninja/masters-thesis/tree/master/src/slides
[REPO-URI-src-thesis   ]: https://github.com/recursion-ninja/masters-thesis/tree/master/src/thesis
