IMPLEMENTATION MODULE SymbolTable;

        (********************************************************)
        (*                                                      *)
        (*            Symbol table for assembler                *)
        (*                                                      *)
        (*  Programmer:         P. Moylan                       *)
        (*  Started:            25 May 1998                     *)
        (*  Last edited:        4 June 1998                     *)
        (*  Status:             OK                              *)
        (*                                                      *)
        (********************************************************)


FROM SYSTEM IMPORT
    (* type *)  CARD8, CARD16;

FROM Output IMPORT
    (* type *)  psecttype,
    (* proc *)  ErrMes, PrintLine;

FROM LowLevel IMPORT
    (* proc *)  HighByte, LowByte;

(************************************************************************)
(*                        THE STRING TABLE                              *)
(************************************************************************)

CONST string_table_size = 32768;

VAR string_table: RECORD
                      nextfree: CARDINAL;
                      val: ARRAY [0..string_table_size - 1] OF CHAR;
                  END (*RECORD*);

(************************************************************************)
(*                        USER SYMBOL TABLE                             *)
(************************************************************************)

CONST SymbolTableSize = 4096;

TYPE Symbol_table_entry = RECORD
                              name: String;
                              defined, equated: BOOLEAN;
                              sym_psect: psecttype;
                              symval: CARD16;
                          END (*RECORD*);

VAR
    FirstPass: BOOLEAN;

    (* Number of symbol table entries. *)

    nsyms: CARDINAL;

    (* The user symbol table. *)

    SymTbl: ARRAY [0..SymbolTableSize-1] OF Symbol_table_entry;

(************************************************************************)
(*                       STRING OPERATIONS                              *)
(************************************************************************)

PROCEDURE AppendToStringTable (VAR (*IN*) source: ARRAY OF CHAR;
                            VAR (*INOUT*) place: CARDINAL): String;

    (* Copies an alphanumeric string from source to the string table,   *)
    (* starting at source[place].  On return, place has been updated    *)
    (* such that source[place] is the first unused character.           *)

    TYPE CharSet = SET OF CHAR;

    CONST AlphaNumeric = CharSet {'A'..'Z', 'a'..'z', '.', '$', '_', '0'..'9'};

    VAR dst, count: CARDINAL;
        ch: CHAR;
        result: String;

    BEGIN
        count := 0;
        dst := string_table.nextfree;
        result.pointer := dst;
        ch := source[place];
        WHILE ch IN AlphaNumeric DO
            INC (count);
            IF dst >= string_table_size THEN
                ErrMes ('O');
            ELSE
                string_table.val[dst] := CAP(ch);
                INC (dst);
            END (*IF*);
            INC (place);
            ch := source[place];
        END (*WHILE*);
        result.length := count;
        RETURN result;
    END AppendToStringTable;

(************************************************************************)

PROCEDURE StringValue (code: String;
                       VAR (*OUT*) result: ARRAY OF CHAR): CARDINAL;

    (* Sets result to the "normal" representation of a string, and      *)
    (* returns its length.                                              *)

    VAR k: CARDINAL;

    BEGIN
        FOR k := 0 TO code.length-1 DO
            IF k <= HIGH(result) THEN
                result[k] := string_table.val[code.pointer+k];
            END (*IF*);
        END (*FOR*);
        k := code.length;
        IF k <= HIGH(result) THEN
            result[k] := CHR(0);
        END (*IF*);
        RETURN code.length;
    END StringValue;

(************************************************************************)

PROCEDURE StringMatch (first: String;  second: ARRAY OF CHAR): BOOLEAN;

    (* Returns TRUE iff the two strings are equal. *)

    VAR j: CARDINAL;

    BEGIN
        j := 0;
        LOOP
           IF (j > HIGH(second)) OR (second[j] = CHR(0)) THEN
               RETURN j >= first.length;
           ELSIF j >= first.length THEN
               RETURN FALSE;
           ELSIF string_table.val[first.pointer+j] <> second[j] THEN
               RETURN FALSE;
           ELSE
               INC (j);
           END (*IF*);
        END (*LOOP*);
    END StringMatch;

(************************************************************************)

PROCEDURE StringIsDot (name: String): BOOLEAN;

    (* Returns TRUE iff name is the string '.' *)

    BEGIN
        RETURN (name.length = 1) AND (string_table.val[name.pointer] = '.');
    END StringIsDot;

(************************************************************************)
(*                      SYMBOL TABLE OPERATIONS                         *)
(************************************************************************)

PROCEDURE addsym (tblptr: CARDINAL;  symbol: String);

    (* Makes room for a new symbol at SymTbl[tblptr], and inserts it.   *)
    (* As a side-effect, string_table.nextfree is updated.  The value   *)
    (* is initialised to zero, the "defined", "equated", and "global"   *)
    (* flags are set FALSE, and we initialise psect to abs_psect.       *)

    VAR j: CARDINAL;

    BEGIN
        IF nsyms = SymbolTableSize THEN
            ErrMes('S');
        ELSE
            (* Make a space in the symbol table. *)

            FOR j := nsyms TO tblptr+1 BY -1 DO
                SymTbl[j] := SymTbl[j-1];
            END (*FOR*);

            (* Insert the new symbol, being careful about flags. *)

            INC (nsyms);
            WITH SymTbl[tblptr] DO
                name := symbol;
                symval := 0;
                defined := FALSE;
                equated := FALSE;
                sym_psect := abs_psect;
            END (*WITH*);

            INC (string_table.nextfree, symbol.length);
        END (*IF*);

    END addsym;

(************************************************************************)

PROCEDURE string_compare (sa, sb: String): INTEGER;

    (* Compares the two strings in the string table.  Returns < 0    *)
    (* if sa < sb, 0 if sa = sb, >0 if sa > sb.                      *)

    VAR j: CARDINAL;  cha, chb: CHAR;

    BEGIN
        j := 0;
        LOOP
            IF j >= sa.length THEN
                IF j >= sb.length THEN
                    RETURN 0;
                ELSE
                    RETURN -1;
                END (*IF*);

            ELSIF j >= sb.length THEN
                RETURN +1;
            ELSE
                cha := string_table.val[sa.pointer+j];
                chb := string_table.val[sb.pointer+j];
                IF cha > chb THEN RETURN +1
                ELSIF cha < chb THEN RETURN -1
                ELSE INC(j);
                END (*IF*);
            END (*IF*);
        END (*LOOP*);
    END string_compare;

(************************************************************************)

PROCEDURE PutHexDigit (value: CARD8;  VAR (*INOUT*) Buffer: ARRAY OF CHAR;
                                      VAR (*INOUT*) position: CARDINAL);

    (* Converts value to hexadecimal, stores result at Buffer[position]. *)

    BEGIN
        IF value < 10 THEN
            Buffer[position] := CHR(ORD('0') + value);
        ELSE
            Buffer[position] := CHR(ORD('A') + value - 10);
        END (*IF*);
        INC (position);
    END PutHexDigit;

(************************************************************************)

PROCEDURE PutHexByte (value: CARD8;  VAR (*INOUT*) Buffer: ARRAY OF CHAR;
                                      VAR (*INOUT*) position: CARDINAL);

    (* Converts value to hexadecimal, stores result at Buffer[position]. *)

    BEGIN
        PutHexDigit (value DIV 16, Buffer, position);
        PutHexDigit (value MOD 16, Buffer, position);
    END PutHexByte;

(************************************************************************)

PROCEDURE PutHexWord (value: CARD16;  VAR (*INOUT*) Buffer: ARRAY OF CHAR;
                                      VAR (*INOUT*) position: CARDINAL);

    (* Converts value to hexadecimal, stores result at Buffer[position]. *)

    BEGIN
        PutHexByte (HighByte(value), Buffer, position);
        PutHexByte (LowByte(value), Buffer, position);
    END PutHexWord;

(************************************************************************)

PROCEDURE PrintSymbolTable;

    (* Sends the symbol table to the listing file. *)

    CONST TabStop = 26;

    VAR j, k, count, SpaceNeeded: CARDINAL;
        Buffer: ARRAY [0..80] OF CHAR;

    BEGIN
        count := 0;
        IF nsyms > 0 THEN
            FOR j := 0 TO nsyms-1 DO

                (* Do we need to start a new line? *)

                SpaceNeeded := 7 + SymTbl[j].name.length;
                SpaceNeeded := TabStop*((SpaceNeeded + TabStop - 1) DIV TabStop);
                IF (count > 0) AND (count + SpaceNeeded > 79) THEN
                    Buffer[count] := CHR(0);
                    PrintLine (Buffer);
                    count := 0;
                END (*IF*);

                (* Tab to a neat position. *)

                WHILE count MOD TabStop <> 0 DO
                    Buffer[count] := ' ';  INC(count);
                END (*WHILE*);

                (* Format the entry for this symbol. *)

                IF SymTbl[j].equated THEN Buffer[count] := '=';
                ELSE Buffer[count] := ' ';
                END (*IF*);
                INC (count);

                IF SymTbl[j].defined THEN
                    PutHexWord (SymTbl[j].symval, Buffer, count);
                ELSE
                    FOR k := 1 TO 4 DO
                        Buffer[count] := '*';  INC(count);
                    END (*FOR*);
                END (*IF*);

                IF SymTbl[j].sym_psect = external_symbol THEN
                     Buffer[count] := 'E';
                ELSIF SymTbl[j].sym_psect = rel_psect THEN
                     Buffer[count] := '"';
                ELSE
                     Buffer[count] := ' ';
                END (*IF*);
                INC (count);
                Buffer[count] := ' ';
                INC (count);

                FOR k := 0 TO SymTbl[j].name.length-1 DO
                    Buffer[count] := string_table.val[SymTbl[j].name.pointer + k];
                    INC (count);
                END (*FOR*);

            END (*FOR*);
        END (*IF*);

        (* Print any partial line remaining. *)

        IF count > 0 THEN
            Buffer[count] := CHR(0);
            PrintLine (Buffer);
        END (*IF*);

        PrintLine ("");
        FirstPass := FALSE;

    END PrintSymbolTable;

(************************************************************************)

PROCEDURE getsym (VAR (*OUT*) symptr: CARDINAL;
                  VAR (*INOUT*) sym_name: String;
                  VAR (*OUT*) sym_value: CARD16;
                  VAR (*OUT*) sym_defined, sym_equated: BOOLEAN;
                  VAR (*OUT*) psect: psecttype);

    (* Gets symbol from user symbol table.  Symbol name is           *)
    (* pointed to by sym_name; value is returned in sym_value,       *)
    (* its place in the symbol table is returned in symptr.  The     *)
    (* Boolean output parameters are set as follows:                 *)
    (*         sym_defined: symbol value is defined.                 *)
    (*         sym_equated: symbol may be updated.                   *)
    (* The symbol table SymTbl is kept sorted.                       *)
    (* Warning: if the symbol is not already in the symbol           *)
    (* table, the symbol in token.TName is inserted.                 *)
    (* Therefore this procedure should not be called with a          *)
    (* so-far-undefined symbol unless that symbol is the last        *)
    (* symbol found by the scanner.                                  *)

    VAR bottom, middle, top: CARDINAL;

    BEGIN
        bottom := 0;
        IF nsyms = 0 THEN
            top := 1;      (* to avoid a spurious "found" *)
        ELSE
            top := nsyms - 1;
            WHILE bottom < top DO
                middle := (bottom + top) DIV 2;
                IF string_compare (SymTbl[middle].name, sym_name) < 0 THEN
                    bottom := middle + 1;
                ELSE
                    top := middle;
                END (*IF*);
            END (*WHILE*);
        END (*IF*);

        (* End of search.  If symbol present, bottom = top and            *)
        (* SymTbl[bottom] is the symbol sought.  Otherwise, the symbol    *)
        (* must be inserted at either SymTbl[bottom] or SymTbl[bottom+1]. *)
        (* Note also the special case corresponding to nsyms = 0.         *)

        IF (bottom = top) AND (string_compare(SymTbl[bottom].name, sym_name) = 0) THEN

            (* Symbol found *)

            symptr := bottom;
            WITH SymTbl[symptr] DO
                sym_name := name;
                sym_value := symval;
                sym_defined := defined;
                sym_equated := equated;
                psect := sym_psect;
            END (*WITH*);

        ELSE               (* symbol not found *)

            IF (nsyms > 0) AND (string_compare(sym_name, SymTbl[bottom].name) > 0) THEN
                INC (bottom);
            END (*IF*);
            symptr := bottom;
            sym_value := 0;
            sym_defined := FALSE;
            sym_equated := FALSE;
            psect := abs_psect;
            addsym (symptr, sym_name);

        END (*IF*);

    END getsym;

(************************************************************************)

PROCEDURE PutSym (symbol_name: String;  symbol_value: CARD16;
                  sym_equated: BOOLEAN;  psect: psecttype);

    (* Puts a symbol into the symbol table.  Its "defined" flag      *)
    (* is set equal to TRUE.                                         *)
    (* N.B. the warning on getsym applies here too.                  *)

    VAR symptr: CARDINAL;
        old_value: CARD16;
        already_defined, was_equated: BOOLEAN;
        old_psect: psecttype;

    BEGIN
        getsym (symptr, symbol_name, old_value, already_defined,
                         was_equated, old_psect);

        (* If the symbol was previously listed as an external symbol, we  *)
        (* are now discovering that it's really an entry symbol.  Thus    *)
        (* we should treat it as a previously undefined symbol.  In       *)
        (* addition, we should put out a global symbol definition record. *)
        (* This should only happen on pass 1 -- by pass 2, the only       *)
        (* external symbols left in the symbol table are those which are  *)
        (* genuinely external.                                            *)

        IF FirstPass AND (old_psect = external_symbol) THEN
            already_defined := FALSE;
            (*
                if (obj_option) {
                        checksum = 0;
                        if (psect == rel_psect)
                                putobject(132, &checksum);
                        else
                                putobject(4, &checksum);
                        putobject((3 + symbol_name.length), &checksum);
                        putobject(symbol_value & 255, &checksum);
                        putobject(shr8(symbol_value), &checksum);
                        putobject(symbol_name.length, &checksum);
                        for (j = -1; j <= (symbol_name.length - 2); j++)
                                putobject(string_table.val[symbol_name.pointer + j], &checksum);
                        temp = checksum;
                        fwrite(&temp, sizeof(byte), 1, object);
                }
             *)
        END (*IF*);

        (* If value is undefined, update the flags.      *)

        IF NOT already_defined THEN
            WITH SymTbl[symptr] DO
                defined := TRUE;
                equated := sym_equated;
                sym_psect := psect;
            END (*WITH*);
        END (*IF*);

        (* Insert the symbol value. *)

        IF already_defined AND (was_equated <> sym_equated) THEN
            ErrMes('M');
        ELSIF already_defined AND NOT sym_equated THEN
            IF old_value <> symbol_value THEN
                ErrMes ('M');
            END (*IF*);
        ELSE
            SymTbl[symptr].symval := symbol_value;
        END (*IF*);

    END PutSym;

(************************************************************************)

BEGIN
    string_table.nextfree := 0;
    nsyms := 0;
    FirstPass := TRUE;
END SymbolTable.

