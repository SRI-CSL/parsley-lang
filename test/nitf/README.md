# Parsley code for NITF: National Imagery Transmission Format

* Specification Documents:
  - [Version 2.1, January 2019](https://github.com/SRI-CSL/parsley-admin/blob/master/papers/nitf/MIL-STD-2500C%20CN2%20Pub%20version%202019-01-02.pdf)
  - [Version 2.1, May 2006](https://github.com/SRI-CSL/parsley-admin/blob/master/papers/nitf/2500C.pdf)

## Notes from January 2019 Spec

### NITF Design Objectives

* To provide a means whereby diverse systems can share imagery and associated data.
* To allow a system to send comprehensive information within one file to users with diverse needs or
capabilities, allowing each user to select only those portions of data that correspond to their needs and capabilities.
* To minimize the cost and schedule required to achieve such capability.

### NITF File Structure.

The NITF file consists of the NITF file header and one or more segment(s). A segment
consists of a sub-header and data fields as shown on FIGURE 3. An example is provided in Appendix E, TABLE E-11.
