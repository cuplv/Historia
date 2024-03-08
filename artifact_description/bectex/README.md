# bectex

Some personal macros and starter files for LaTeX projects.

## Typical Usage

After starting a new git repository for a paper (e.g., via `git init`), add a submodule reference to this repository.

```bash
~/paper (master)$ git submodule add https://github.com/cuplv/bectex.git
```

Then, symlink (or copy) the desired files from `bectex/` into the root directory. The command

```bash
~/paper (master)$ make -f bectex/bectex.mk init
```

will copy the editable `Makefile` and symlink all other files.

Currently, the `Makefile` mostly delegates to [Latexmk] (which comes with [MacTeX]) to do the work.

[Latexmk]: https://www.ctan.org/pkg/latexmk
[MacTeX]: https://www.tug.org/mactex/

## Bibliography

This package provides a super simplistic way of managing BibTeX references. The `Makefile` expects BibTeX databases in `*.orig.bib` that uses `@string`s for conference names. The file `conference.orig.bib` lists a number of `@string` macros for conference names with variants for level of abbreviation.

For consistent BibTeX entries, I use [DBLP] entries whenever possible with minimal editing. To manage BibTeX files, I use [BibDesk] (which also comes with [MacTeX]). It is easy to use the web browser inside BibDesk with DBLP. If you are on a DBLP page with a BibTeX entry, you can directly import into your open BibTeX database.

[DBLP]: http://dblp.org/
[BibDesk]: http://bibdesk.sourceforge.net/

### Editing for Conference Names

The one bit of editing that is necessary after importing an entry from DBLP is to change the conference name to use a `@string` conference name macro in `conference.orig.bib`.

### Generating Shortened Bibliographies

The `Makefile` generates `%.short.bib` from `%.orig.bib` files, so you can edit it to do whatever desired processing. A simple, hacky `sed` script is usually sufficient.

## LaTeX Packages

The `bec.sty` file simply collects together some personal macros along with usage of various LaTeX packages.

## Tools

### MacTeX with BibDesk

```bash
$ brew cask install mactex
```
