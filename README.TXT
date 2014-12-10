8080/8085 Cross-assembler
=========================

Sorry, this program comes without documentation.  The
way to resolve questions is to look at the source
listings.

There are two versions.  The one in the DOS directory
is for DOS/Windows.  The one in the OS2 directory is
for OS/2.  The OS/2 version is the one that's most
easily ported to other operating systems.

You run the assembler with a command of the form
     AS85 PROG.ASM

This will then create output files PROG.LST and PROG.HEX.
(There should also be a way to produce standard OBJ
file format, but in this version that's disabled; I
didn't have time to finish that job.)

The assembly language accepted is the complete 8085
instruction set, plus the directives
        .ABS
        .ASCII
        .BYTE
        .END
        .GLOBL
        .PAGE
        .REL
        .WORD

Peter Moylan       peter@ee.newcastle.edu.au
3 June 1998
