# An interpreter for a subset of MetaOCaml in Silver

This repository contains an interpreted implementation of a subset of MetaOCaml
as a demonstration of the reflection capabilities of Silver.

## Authors
- Lucas Kramer, University of Minnesota, krame505@umn.edu
  ORCID: https://orcid.org/0000-0001-6719-6894
- Eric Van Wyk, University of Minnesota, evw@umn.edu,
  ORCID: https://orcid.org/0000-0002-5611-8687

## Releases
- Release 0.1.0: made in September, 2019
- Release 0.1.1: made in April, 2020

## License
This software is distributed under the GNU Lesser General Public License. See the file LICENSE for details.  
More information can be found at http://www.gnu.org/licenses/.

## Related publications
Release 0.1.1 is discussed in the paper "Reflection of Terms in Attribute Grammars: Design and Applications" by Lucas Kramer, Ted Kaminski, and Eric Van Wyk.  At the time of release this paper has been submitted to the Journal of Computer Languages (COLA).  

It is an extension of ``Reflection in Attribute Grammars'' by the same
authors, presented at the 2019 ACM SIGPLAN
International Conference on Generative Programming: Concepts &
Experiences (GPCE).  See DOI https://doi.org/10.1145/3357765.3359517.
This paper references release 0.1.0 of this software.

## Repositories
- Actively-developed versions of this software are available on GitHub at https://github.com/melt-umn/meta-ocaml-lite
- Archival versions of this software are permanently available on the Data Repository of the University of Minnesota at https://doi.org/10.13020/z10a-7g60.

# Using the Software
To see how the Silver reflection features can be used, see the Silver specification in the ``grammars`` directory.  Specifically, the files ``Expr.sv`` and ``Value.sv`` in the ``grammars/edu.umn.cs.melt.metaocaml/abstractsyntax`` directory.  This material is discussed in the paper mentioned above.

A ``build`` script will create the Silver evaluation for this and the ``run-tests`` will execute it on some provided test files.

Be sure that Silver version 0.4.2 is used since it contains the new reflection features used here.

## Required Software
- Silver version 0.4.2.  Availble at https://melt.cs.umn.edu/silver and archived at https://doi.org/10.13020/D6QX07.
