# An implementation of Caml Light in Silver.

This repository contains an implementation of type inference in the
Caml Light language that uses the implicit-monads extension to Silver.


## Authors
- Dawn Michaelson, University of Minnesota, micha576@umn.edu
- Eric Van Wyk, University of Minnesota, evw@umn.edu,
  ORCID: https://orcid.org/0000-0002-5611-8687


## Releases
- Release 0.1.0: made in October 2020


## License
This software is distributed under the GNU Lesser General Public License. See the file LICENSE for details.
More information can be found at http://www.gnu.org/licenses/.

## Related publications
Release 0.1.0 is discussed in the paper "Monadification of Attribute
Grammars" by Dawn Michaelson and Eric Van Wyk.  At the time of
release, this paper has been accepted to the ACM Software Language
Engineering conference.


## Repositories
- Actively-developed versions of this software are available on GitHub
  at https://github.com/melt-umn/caml-light
- Archival versions of this software are permanently available on the
  Data Repository of the University of Minnesota


# Using the Software
To see how the Silver implicit monads features can be used, see the
Silver specification in the `grammars/abstractSyntax` directory.  This
material is discussed in the paper mentioned above.

The `silver-compile` script will create the Silver executable for
this, a JAR file.  The JAR file can be used to execute the examples in
the `sample_programs` directory.

