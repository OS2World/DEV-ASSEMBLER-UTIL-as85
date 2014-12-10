IMPLEMENTATION MODULE Output;

        (********************************************************)
        (*                                                      *)
        (*       Listfile and object output for assembler       *)
        (*                                                      *)
        (*  Programmer:         P. Moylan                       *)
        (*  Started:            25 May 1998                     *)
        (*  Last edited:        4 June 1998                     *)
        (*  Status:             OK                              *)
        (*                                                      *)
        (*    NOTE: It's so long that anyone has had a need     *)
        (*    to use the binary object option that it's not     *)
        (*    adequately tested.  (Everyone seems to want       *)
        (*    only the hex output option, and that's working.)  *)
        (*                                                      *)
        (********************************************************)


FROM SYSTEM IMPORT
    (* type *)  CARD8, CARD16;

IMPORT IOChan, ChanConsts, SeqFile, FileSys, RawIO, Strings;

FROM TextIO IMPORT
    (* proc *)  WriteChar, WriteString, WriteLn;

FROM LowLevel IMPORT
    (* proc *)  HighByte, LowByte, IXORB;

(************************************************************************)

CONST
    codebufferlimit = 31;

TYPE
    FileNameString = ARRAY [0..511] OF CHAR;

VAR
    (* Location counter. *)

    LocCtr: ARRAY psecttype OF CARD16;
    current_psect: psecttype;

    (* Output files. *)

    ListFileOpen, HexFileOpen, ObjectFileOpen: BOOLEAN;
    ListFileName, HexFileName, ObjectFileName: FileNameString;
    listing, hexfile, objectfile: IOChan.ChanId;

    (* A buffer to hold the "preamble" part of a listing line. *)

    ListBuffer: RECORD
                    err: CHAR;                 (* Error code               *)
                    LC: ARRAY [0..3] OF CHAR;  (* Location counter (hex)   *)
                    LCflag: CHAR;              (* Flag for LC relative.    *)
                    code: ARRAY [1..3] OF
                          ARRAY [0..1] OF CHAR;(* Hex object code          *)
                    codeflag: CHAR;            (* Flag relocation of code. *)
                END (*RECORD*);

    (* The number of characters so far printed on the current line *)
    (* of the hex output file.                                     *)

    op_line_length: CARDINAL;

    (* Count of the number of source code errors reported. *)

    ErrCount: CARDINAL;

    (* Object code buffers.  *)

    CodeBuffer: RECORD
                    ExpectedPsect: psecttype;
                    StartLC, ExpectedLC: CARD16;
                    val: ARRAY [0..codebufferlimit] OF CARD8;
                END (*RECORD*);

    RLDbuffer: RECORD
                   count: CARDINAL;
                   val: ARRAY [0..codebufferlimit] OF CARD8;
               END (*RECORD*);

(************************************************************************)
(*                        ENABLING THE OUTPUT                           *)
(************************************************************************)

PROCEDURE SetOutputFileNames (VAR (*IN*) srcname: ARRAY OF CHAR);

    (* Sets listing and object file names, based on a given source *)
    (* file name.                                                  *)

    VAR found: BOOLEAN;  position: CARDINAL;

    BEGIN
        Strings.Assign (srcname, ListFileName);

        IF ListFileName[0] <> CHR(0) THEN
            (* Strip off any existing filename extension. *)
    
            Strings.FindPrev ('.', ListFileName, LENGTH(ListFileName)-1,
                                   found, position);
            IF found THEN
                ListFileName[position] := CHR(0);
            END (*IF*);
        END (*IF*);

        (* Make the extensions ".LST", ".HEX", and "OBJ" *)

        HexFileName := ListFileName;
        ObjectFileName := ListFileName;
        Strings.Append (".LST", ListFileName);
        Strings.Append (".HEX", HexFileName);
        Strings.Append (".OBJ", ObjectFileName);

    END SetOutputFileNames;

(************************************************************************)

PROCEDURE OpenOutputFiles (list, hex: BOOLEAN);

    (* Opens the listing and/or hex code files.         *)
    (* Also clears the count of the number of errors.   *)

    VAR res: ChanConsts.OpenResults;  dummy: BOOLEAN;

    BEGIN
        ErrCount := 0;
        ListFileOpen := list;
        IF list THEN
            FileSys.Remove (ListFileName, dummy);
            SeqFile.OpenWrite (listing, ListFileName,
                        SeqFile.write + SeqFile.text, res);
        END (*IF*);
        HexFileOpen := hex;
        IF hex THEN
            FileSys.Remove (HexFileName, dummy);
            SeqFile.OpenWrite (hexfile, HexFileName,
                        SeqFile.write + SeqFile.text, res);
        END (*IF*);
    END OpenOutputFiles;

(************************************************************************)

PROCEDURE WriteCard (cid: IOChan.ChanId;  value: CARDINAL);

    (* Writes a decimal number to the file. *)

    BEGIN
        IF value > 9 THEN
            WriteCard (cid, value DIV 10);
        END (*IF*);
        WriteChar (cid, CHR(ORD('0') + value MOD 10));
    END WriteCard;

(************************************************************************)

PROCEDURE CloseOutputFiles(): CARDINAL;

    (* If any output files are open, closes them.  As a side-effect,    *)
    (* returns the error count.                                         *)

    BEGIN
        IF ListFileOpen THEN
            WriteLn (listing);
            IF ErrCount = 0 THEN
                WriteString (listing, " No errors.");
            ELSE
                WriteCard (listing, ErrCount);
                WriteString (listing, " errors.");
            END (*IF*);
            WriteLn (listing);
            WriteLn (listing);
            SeqFile.Close (listing);
            ListFileOpen := FALSE;
        END (*IF*);

        IF HexFileOpen THEN
            IF op_line_length >= 16 THEN
                WriteLn (hexfile);
                op_line_length := 0;
            END (*IF*);
            SeqFile.Close (hexfile);
            HexFileOpen := FALSE;
        END (*IF*);

        RETURN ErrCount;

    END CloseOutputFiles;

(************************************************************************)

PROCEDURE PrintLine (line: ARRAY OF CHAR);

    (* Sends a line of text to the listing file. *)

    BEGIN
        WriteString (listing, line);
        WriteLn (listing);
    END PrintLine;

(************************************************************************)
(*                     HEX-TO-STRING CONVERSIONS                        *)
(************************************************************************)

PROCEDURE HexDigit (number: CARD8): CHAR;

    (* Converts number (range [0..15]) to a hexadecimal code. *)

    BEGIN
        IF number < 10 THEN
            RETURN CHR (ORD('0') + number);
        ELSE
            RETURN CHR (ORD('A') + number - 10);
        END (*IF*);
    END HexDigit;

(************************************************************************)

PROCEDURE StoreHexByte (value: CARD8;  VAR (*OUT*) result: ARRAY OF CHAR;
                                       place: CARDINAL);

    (* Puts a 2-character hexadecimal number in result, starting        *)
    (* at result[place].                                                *)

    BEGIN
        result[place]   := HexDigit (value DIV 16);
        result[place+1] := HexDigit (value MOD 16);
    END StoreHexByte;

(************************************************************************)

PROCEDURE StoreHexWord (value: CARD16;  VAR (*OUT*) result: ARRAY OF CHAR);

    (* Puts a 4-character hexadecimal number in result. *)

    BEGIN
        StoreHexByte (HighByte (value), result, 0);
        StoreHexByte (LowByte (value), result, 2);
    END StoreHexWord;

(************************************************************************)
(*                  OPERATIONS ON THE LOCATION COUNTER                  *)
(************************************************************************)

PROCEDURE ClearLocationCounter;

    (* Sets the location counter to an initial default. *)

    BEGIN
        LocCtr[abs_psect] := 0;
        LocCtr[rel_psect] := 0;
        current_psect := abs_psect;
    END ClearLocationCounter;

(************************************************************************)

PROCEDURE IncrementLocationCounter;

    (* Adds 1 to the current location counter. *)

    VAR LC: CARD16;

    BEGIN
        LC := LocCtr[current_psect];
        IF LC = MAX(CARDINAL) THEN
            LC := 0;
        ELSE
            INC (LC);
        END(*IF*);
        LocCtr[current_psect] := LC;
    END IncrementLocationCounter;

(************************************************************************)

PROCEDURE SetLocationCounter (value: CARD16;  psect: psecttype);

    (* Gives a new value to the location counter and current psect. *)

    BEGIN
        IF psect <> current_psect THEN
            ErrMes('X');
            current_psect := psect;
        END (*IF*);
        LocCtr[current_psect] := value;
    END SetLocationCounter;

(************************************************************************)

PROCEDURE ReadLocationCounter (VAR (*OUT*) value: CARD16;
                               VAR (*OUT*) psect: psecttype);

    (* Returns the current value of the location counter and psect. *)

    BEGIN
        psect := current_psect;
        value := LocCtr[psect];
    END ReadLocationCounter;

(************************************************************************)

PROCEDURE SetPsect (psect: psecttype);

    (* Switches to a new psect. *)

    BEGIN
        current_psect := psect;
    END SetPsect;

(************************************************************************)
(*                       ERROR MESSAGE OUTPUT                           *)
(************************************************************************)

PROCEDURE ErrMes (code: CHAR);

    (* Error message routine.  Will only log the first error on each line. *)

    BEGIN
        IF ListBuffer.err = ' ' THEN
            ListBuffer.err := code;
            INC (ErrCount);
        END (*IF*);
    END ErrMes;

(************************************************************************)
(*                    PUTTING OUT THE LISTING                           *)
(************************************************************************)

PROCEDURE ClearPreamble;

    (* Resets the listing buffer. *)

    VAR j: [1..3];

    BEGIN
        WITH ListBuffer DO
            err := ' ';
            LC := "    ";
            LCflag := ' ';
            FOR j := 1 TO 3 DO
                code[j] := "  ";
            END (*FOR*);
            codeflag := ' ';
        END (*WITH*);
    END ClearPreamble;

(************************************************************************)

PROCEDURE PrtLC;

    (* Puts the location counter (in hex) into the listing buffer. *)

    BEGIN
        StoreHexWord (LocCtr[current_psect], ListBuffer.LC);
        IF current_psect = rel_psect THEN
            ListBuffer.LCflag := '"';
        END (*IF*);
    END PrtLC;

(************************************************************************)

PROCEDURE ListTheLine (VAR (*IN*) sourceline: ARRAY OF CHAR);

    (* Puts the current line out to the listing file. *)

    VAR j: [1..3];

    BEGIN
        IF ListFileOpen THEN
            WITH ListBuffer DO
                WriteChar (listing, err);
                WriteChar (listing, ' ');
                WriteString (listing, LC);
                WriteChar (listing, LCflag);
                WriteString (listing, code[1]);
                WriteChar (listing, ' ');
                WriteString (listing, code[2]);
                WriteChar (listing, ' ');
                WriteString (listing, code[3]);
                WriteChar (listing, codeflag);
            END (*WITH*);
            WriteString (listing, sourceline);
            WriteLn (listing);

        END (*IF*);

        IF HexFileOpen THEN

            FOR j := 1 TO 3 DO

                IF ListBuffer.code[j][1] <> ' ' THEN
                    WriteString (hexfile, ListBuffer.code[j]);
                    INC (op_line_length);
                END (*IF*);

                IF op_line_length >= 16 THEN
                    WriteLn (hexfile);
                    op_line_length := 0;
                END (*IF*);

            END (*FOR*);

        END (*IF*);

    END ListTheLine;

(************************************************************************)
(*                          BINARY OUTPUT                               *)
(************************************************************************)

PROCEDURE InitBinout;

    (* Sets up the initial conditions for binary output. *)

    BEGIN
        CodeBuffer.ExpectedPsect := abs_psect;
        CodeBuffer.StartLC := 0;
        CodeBuffer.ExpectedLC := 0;
        RLDbuffer.count := 0;
    END InitBinout;

(************************************************************************)

PROCEDURE putobject (value: CARD8;  VAR (*INOUT*) checksum: CARD8);

    (* Puts a byte out to the object file, and updates       *)
    (* the checksum.                                         *)

    VAR buffer: ARRAY [0..0] OF CARD8;

    BEGIN
        IF ObjectFileOpen THEN
            buffer[0] := value;
            RawIO.Write (objectfile, buffer);
        END (*IF*);
        checksum := IXORB (checksum, value);
    END putobject;

(************************************************************************)

PROCEDURE FlushBuffer;

    (* Sends the current contents of the binary output buffer *)
    (* to the object file.                                    *)

    VAR checksum: CARD8;  j: CARDINAL;

    BEGIN

        IF CodeBuffer.StartLC <> CodeBuffer.ExpectedLC THEN

            (* Write the record header and byte count.  *)

            checksum := 0;
            IF CodeBuffer.ExpectedPsect = abs_psect THEN
                putobject (2, checksum);
            ELSE
                putobject (130, checksum);
            END (*IF*);
            putobject((CodeBuffer.ExpectedLC - CodeBuffer.StartLC + 2), checksum);

            (* Then the load address.        *)

            putobject (LowByte (CodeBuffer.StartLC), checksum);
            putobject (HighByte (CodeBuffer.StartLC), checksum);

            (* Now the binary data.  *)

            FOR j := 0 TO CodeBuffer.ExpectedLC - CodeBuffer.StartLC - 1 DO
                putobject (CodeBuffer.val[j], checksum);
            END (*IF*);

            (* Finally, the checksum.        *)

            putobject (checksum, checksum);

        END (*IF*);

        CodeBuffer.StartLC := LocCtr[current_psect];
        CodeBuffer.ExpectedLC := LocCtr[current_psect];
        CodeBuffer.ExpectedPsect := current_psect;

        (* Flush the RLD buffer.         *)

        IF RLDbuffer.count <> 0 THEN

            (* Write the record header and byte count.       *)

            checksum := 0;
            putobject (3, checksum);
            putobject (RLDbuffer.count, checksum);

            (* Now the binary data.  *)

            FOR j := 0 TO RLDbuffer.count - 1 DO
                putobject (RLDbuffer.val[j], checksum);
            END (*IF*);

            (* Finally, the checksum.        *)

            putobject (checksum, checksum);
            RLDbuffer.count := 0;

        END (*IF*);

    END FlushBuffer;

(************************************************************************)

PROCEDURE binout (value: CARD8;  word_flag: BOOLEAN;
                         psect: psecttype;  symbol: ARRAY OF CHAR);

    (* Puts a byte into the binary output buffer.  If necessary,     *)
    (* flushes the output buffer before starting a new               *)
    (* buffer-full.  If word_flag is true, this indicates that       *)
    (* this is the first byte of a word.                             *)

    VAR new_record_needed: BOOLEAN;
        j, offset, sub_record_kind, RLD_space_needed: CARD8;

    BEGIN
        (* Work out what sort of relocation record is needed.    *)

        sub_record_kind := 0;
        RLD_space_needed := 0;
        IF psect = rel_psect THEN
            sub_record_kind := 1;
            RLD_space_needed := 2;
        ELSIF psect = external_symbol THEN
            sub_record_kind := 2;
            RLD_space_needed := 3 + LENGTH(symbol);
        END (*IF*);
        IF word_flag AND (psect <> abs_psect) THEN
            INC (sub_record_kind, 128);
        END (*IF*);

        (* Work out whether a new record has to be started.      *)

        offset := LocCtr[current_psect] - CodeBuffer.StartLC;
        new_record_needed := (LocCtr[current_psect] <> CodeBuffer.ExpectedLC)
                OR (current_psect <> CodeBuffer.ExpectedPsect)
                OR (offset > codebufferlimit)
                OR (word_flag AND (offset = codebufferlimit))
                OR (RLD_space_needed > (RLDbuffer.count + codebufferlimit));
        IF new_record_needed THEN
            FlushBuffer();
            offset := 0;
        END (*IF*);

        (* Put the new byte into the buffer.     *)

        CodeBuffer.val[offset] := value;
        CodeBuffer.ExpectedLC := LocCtr[current_psect] + 1;

        (* Put whatever is needed into the relocation buffer.    *)

        IF sub_record_kind <> 0 THEN
            RLDbuffer.val[RLDbuffer.count] := sub_record_kind;
            INC (RLDbuffer.count);
            RLDbuffer.val[RLDbuffer.count] := offset;
            INC (RLDbuffer.count);
            IF psect = external_symbol THEN
                RLDbuffer.val[RLDbuffer.count] := LENGTH(symbol);
                INC (RLDbuffer.count);
                FOR j := 0 TO LENGTH(symbol)-1 DO
                    RLDbuffer.val[RLDbuffer.count] := ORD(symbol[j]);
                    INC (RLDbuffer.count);
                END (*FOR*);
            END (*IF*);
        END (*IF*);

    END binout;

(************************************************************************)

PROCEDURE PutObjectCode (opcode: CARD8;  place: CARDINAL;
                            word_flag: BOOLEAN;  psect: psecttype);

    (* Puts code out to the listing and object files.  *)

    BEGIN
        StoreHexByte (opcode, ListBuffer.code[place], 0);
        IF psect <> abs_psect THEN
            ListBuffer.codeflag := '"';
        END (*IF*);
        IF ObjectFileOpen THEN
            binout (opcode, word_flag, psect, "");
        END (*IF*);
    END PutObjectCode;

(************************************************************************)

BEGIN
    ErrCount := 0;
    op_line_length := 0;
    ListFileOpen := FALSE;  HexFileOpen := FALSE;  ObjectFileOpen := FALSE;
    InitBinout;
END Output.

