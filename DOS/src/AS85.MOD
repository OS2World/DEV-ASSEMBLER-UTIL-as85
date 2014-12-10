MODULE as85;

        (********************************************************)
        (*                                                      *)
        (*               8085 cross-assembler                   *)
        (*                                                      *)
        (*        (DOS version, compiled with TopSpeed)         *)
        (*                                                      *)
        (*  Programmer:         P. Moylan                       *)
        (*  Started:            25 May 1998                     *)
        (*  Last edited:        3 June 1998                     *)
        (*  Status:             OK                              *)
        (*                                                      *)
        (*    MISSING FEATURE: In this version, nothing is      *)
        (*    going to the binary object file.  Instead,        *)
        (*    the output goes to the hex output file.           *)
        (*    For now this is all that is needed, but I         *)
        (*    should fill in the details for binary object      *)
        (*    format as well, before everyone has forgotten     *)
        (*    how that format works.                            *)
        (*                                                      *)
        (*  This assembler has a rather long history.  The      *)
        (*  original version was written in SGL by Peter        *)
        (*  Moylan, and subsequently translated into Pascal.    *)
        (*  Those early versions appear to be lost.             *)
        (*                                                      *)
        (*  In about 1991 Viktor Holmberg translated the code   *)
        (*  into C, presumably because a Pascal compiler was    *)
        (*  not available for whatever machine Viktor was       *)
        (*  using.  That C version was later maintained by      *)
        (*  Tim Wiley.                                          *)
        (*                                                      *)
        (*  In 1998 we had some problems with errors, and       *)
        (*  nobody was quite sure where the fault was.          *)
        (*  I decided that it was easier to rewrite the         *)
        (*  program than try to debug C code, so I've           *)
        (*  translated the whole thing into Modula-2.  The      *)
        (*  code is a translation rather than a re-design,      *)
        (*  but I think I've managed to clean up some things    *)
        (*  while doing the translation.                        *)
        (*                                                      *)
        (********************************************************)

IMPORT FIO;

FROM IO IMPORT
    (* proc *)  WrStr, WrCard, WrLn;

FROM LowLevel IMPORT
    (* proc *)  IAND, LowByte, HighByte;

FROM SymbolTable IMPORT
    (* type *)  String,
    (* proc *)  AppendToStringTable, StringMatch, StringIsDot,
                StringValue,
                getsym, PutSym, PrintSymbolTable;

FROM Output IMPORT
    (* type *)  psecttype,
    (* proc *)  SetOutputFileNames, OpenOutputFiles, CloseOutputFiles,
                ClearPreamble, ErrMes, PrtLC, ListTheLine,
                PutObjectCode, putobject, FlushBuffer,
                ClearLocationCounter, IncrementLocationCounter,
                SetPsect, SetLocationCounter, ReadLocationCounter;

FROM Lib IMPORT
    (* proc *)  ParamCount, ParamStr;

(************************************************************************)
(*                        GLOBAL VARIABLES                              *)
(************************************************************************)

CONST Nul = CHR(0);  Tab = CHR(9);  Space = ' ';

TYPE CARD16 = CARDINAL;

VAR
    (* Program start address. *)

    StartAddress: RECORD
                      Supplied: BOOLEAN;
                      val: CARD16;
                      psect: psecttype;
                  END (*RECORD*);

    (* Assembly pass. *)

    pass: [1..2];

    (* Output options. *)

    obj_option, list_option: BOOLEAN;

    (* End-of-source-file flag.  *)

    EndFlag: BOOLEAN;

    (* Current source token. *)

    token: RECORD
               TCode, LookAhead: CHAR;
               TName: String;
               TValue: CARD16;
           END (*RECORD*);

    (* Scanner persistent variables. *)

    srchandle: FIO.File;
    SourceName: ARRAY [0..79] OF CHAR;

    SrcPtr: CARDINAL;

    SrcBuf: ARRAY [0..1023] OF CHAR;
    SourceFileBuffer: ARRAY [1..2048+FIO.BufferOverhead] OF BYTE;

(************************************************************************)
(*                         GLOBAL TABLES                                *)
(************************************************************************)

CONST
    NumberOfMnemonics = 88;

TYPE
    CARD8 = SHORTCARD;

    SixChar = ARRAY [0..5] OF CHAR;

    ORec =                RECORD
                              mnem: SixChar;
                              i_code: CARD8;
                              i_class: INTEGER;
                          END (*RECORD*);

    OpCodeTableType = ARRAY [0..NumberOfMnemonics-1] OF ORec;

CONST
    RegisterList = "BCDEHLMAFSP";

    OpCodes = OpCodeTableType
                 (
                       ORec(".ABS  ", 0, -6),
                       ORec(".ASCII", 0, -3),
                       ORec(".BYTE ", 0, -1),
                       ORec(".END  ", 0, -5),
                       ORec(".GLOBL", 0, -8),
                       ORec(".PAGE ", 0, -4),
                       ORec(".REL  ", 0, -7),
                       ORec(".WORD ", 0, -2),
                       ORec("ACI   ", 206, 9),
                       ORec("ADC   ", 136, 13),
                       ORec("ADD   ", 128, 13),
                       ORec("ADI   ", 198, 9),
                       ORec("ANA   ", 160, 13),
                       ORec("ANI   ", 230, 9),
                       ORec("CALL  ", 205, 11),
                       ORec("CC    ", 220, 11),
                       ORec("CM    ", 252, 11),
                       ORec("CMA   ", 47, 1),
                       ORec("CMC   ", 63, 1),
                       ORec("CMP   ", 184, 13),
                       ORec("CNC   ", 212, 11),
                       ORec("CNZ   ", 196, 11),
                       ORec("CP    ", 244, 11),
                       ORec("CPE   ", 236, 11),
                       ORec("CPI   ", 254, 9),
                       ORec("CPO   ", 228, 11),
                       ORec("CZ    ", 204, 11),
                       ORec("DAA   ", 39, 1),
                       ORec("DAD   ", 9, 5),
                       ORec("DCR   ", 5, 2),
                       ORec("DCX   ", 11, 5),
                       ORec("DI    ", 243, 1),
                       ORec("EI    ", 251, 1),
                       ORec("HLT   ", 118, 1),
                       ORec("IN    ", 219, 10),
                       ORec("INR   ", 4, 2),
                       ORec("INX   ", 3, 5),
                       ORec("JC    ", 218, 11),
                       ORec("JM    ", 250, 11),
                       ORec("JMP   ", 195, 11),
                       ORec("JNC   ", 210, 11),
                       ORec("JNZ   ", 194, 11),
                       ORec("JP    ", 242, 11),
                       ORec("JPE   ", 234, 11),
                       ORec("JPO   ", 226, 11),
                       ORec("JZ    ", 202, 11),
                       ORec("LDA   ", 58, 11),
                       ORec("LDAX  ", 10, 7),
                       ORec("LHLD  ", 42, 11),
                       ORec("LXI   ", 1, 12),
                       ORec("MOV   ", 64, 4),
                       ORec("MVI   ", 6, 8),
                       ORec("NOP   ", 0, 1),
                       ORec("ORA   ", 176, 13),
                       ORec("ORI   ", 246, 9),
                       ORec("OUT   ", 211, 10),
                       ORec("PCHL  ", 233, 1),
                       ORec("POP   ", 193, 6),
                       ORec("PUSH  ", 197, 6),
                       ORec("RAL   ", 23, 1),
                       ORec("RAR   ", 31, 1),
                       ORec("RC    ", 216, 1),
                       ORec("RET   ", 201, 1),
                       ORec("RIM   ", 32, 1),
                       ORec("RLC   ", 7, 1),
                       ORec("RM    ", 248, 1),
                       ORec("RNC   ", 208, 1),
                       ORec("RNZ   ", 192, 1),
                       ORec("RP    ", 240, 1),
                       ORec("RPE   ", 232, 1),
                       ORec("RPO   ", 224, 1),
                       ORec("RRC   ", 15, 1),
                       ORec("RST   ", 199, 3),
                       ORec("RZ    ", 200, 1),
                       ORec("SBB   ", 152, 13),
                       ORec("SBI   ", 222, 9),
                       ORec("SHLD  ", 34, 11),
                       ORec("SIM   ", 48, 1),
                       ORec("SPHL  ", 249, 1),
                       ORec("STA   ", 50, 11),
                       ORec("STAX  ", 2, 7),
                       ORec("STC   ", 55, 1),
                       ORec("SUB   ", 144, 13),
                       ORec("SUI   ", 214, 9),
                       ORec("XCHG  ", 235, 1),
                       ORec("XRA   ", 168, 13),
                       ORec("XRI   ", 238, 9),
                       ORec("XTHL  ", 227, 1)
                 );

(************************************************************************)
(*                        16-BIT ARITHMETIC                             *)
(************************************************************************)

PROCEDURE Add16 (first, second: CARD16): CARD16;

    (* 16-bit addition, with overflow check.  We have to be generous    *)
    (* about the meaning of "overflow", because we don't know whether   *)
    (* the arithmetic is supposed to be signed or unsigned.  The only   *)
    (* overflow case is where the two numbers both have their high      *)
    (* order bits set, and the sum truncated to 16 bits has its high    *)
    (* order bit clear.  Every other case is valid according to the     *)
    (* rules of unsigned arithmetic, or the rules of twos complement    *)
    (* arithmetic, or both.                                             *)

    CONST limit = MAX(CARD16) DIV 2;

    VAR result: LONGCARD;

    BEGIN
        result := LONGCARD(first) + LONGCARD(second);
        IF result > MAX(CARD16) THEN
            DEC (result, MAX(CARD16)+1);
        END (*IF*);
        IF (first > limit) AND (second > limit) AND (result < limit) THEN
            ErrMes('V');
        END (*IF*);
        RETURN CARD16(result);
    END Add16;

(************************************************************************)

PROCEDURE Sub16 (first, second: CARD16): CARD16;

    (* 16-bit subtraction, with overflow check. *)

    VAR temp: LONGCARD;

    BEGIN
        temp := 65536 - LONGCARD(second);
        RETURN Add16 (first, CARD16 (temp));
    END Sub16;

(************************************************************************)
(*                          SCANNER                                     *)
(************************************************************************)

PROCEDURE InitScanner;

    BEGIN
        token.TCode := Nul;
        srchandle := FIO.Open (SourceName);
        FIO.AssignBuffer (srchandle, SourceFileBuffer);
    END InitScanner;

(************************************************************************)

PROCEDURE LineIn;

    BEGIN
        (* Clear the error code, etc., part of the buffer. *)

        ClearPreamble();

        (* Now read the source line. *)

        FIO.RdStr (srchandle, SrcBuf);

        (* Result is set to the value allRight, endOfLine, or endOfInput. *)
(*
        result := IOChan.ReadResult (srchandle);
        IF result = IOConsts.endOfInput THEN

            (* Premature end of file. *)

            ErrMes('E');
            SrcBuf := "";
            EndFlag := TRUE;

        ELSIF result <> IOConsts.endOfLine THEN

            (* Check that we got the whole line. *)

            TextIO.ReadString (srchandle, dummy);
            IF dummy[0] <> Nul THEN
                ErrMes ('L');
            END (*IF*);

        END (*IF*);
*)
    END LineIn;

(************************************************************************)

PROCEDURE skipblank;

    BEGIN
        WHILE ((SrcBuf[SrcPtr] = Space) OR (SrcBuf[SrcPtr] = Tab)) DO
            INC (SrcPtr);
        END (*WHILE*);
    END skipblank;

(************************************************************************)

PROCEDURE scan;

    TYPE CharSet = SET OF CHAR;

    CONST Letters = CharSet {'A'..'Z', 'a'..'z', '.', '$', '_'};
          Digits = CharSet {'0'..'9'};
          HexDigits = CharSet {'0'..'9', 'a'..'f', 'A'..'F'};
          FF = CHR(12);

    VAR count, radix, j: CARDINAL;  ch: CHAR;

    BEGIN
        (* If token = Nul (from the last scan), we   *)
        (* need to get in a new line.                *)

        IF token.TCode = Nul THEN
            LineIn();
            SrcPtr := 0;
        END (*IF*);

        (* Skip leading blanks.  Note that we don't skip blank lines,    *)
        (* since the routine responsible for listing will want to        *)
        (* know about them.                                              *)

        skipblank();
        ch := SrcBuf[SrcPtr];
        INC (SrcPtr);

        IF ch = ';' THEN ch := Nul;

        (* Check for identifier.  If found, put the name into the string *)
        (* table, and a pointer to it into token.TName.                  *)

        ELSIF ch IN Letters THEN
            DEC (SrcPtr);
            token.TName := AppendToStringTable (SrcBuf, SrcPtr);
            ch := 'A';

            (* Skip trailing blanks, put a lookahead symbol  *)
            (* into LookAhead (for use by label and primary)         *)

            skipblank();
            token.LookAhead := SrcBuf[SrcPtr];
            IF (token.LookAhead <> ':') AND (token.LookAhead <> '=')
                              AND (token.LookAhead <> '(') THEN
                token.LookAhead := ' ';
            END (*IF*);

        ELSIF ch = FF THEN
            ch := Nul;

        (* Check for number.  note that because of the order in which    *)
        (* the checking is done, numbers may not start with A..F.        *)

        ELSIF ch IN Digits THEN

            (* First, count the number of digits *)

            count := 0;
            WHILE ch IN HexDigits DO
                INC (count);
                ch := SrcBuf[SrcPtr];
                INC (SrcPtr);
            END (*WHILE*);

            (* Work out the radix.  *)

            IF ch = '#' THEN radix := 2;
            ELSIF ch = 'Q' THEN radix := 8;
            ELSIF ch = '.' THEN radix := 10;
            ELSE radix := 16;
            END (*IF*);

            (* Now go back and convert the number to binary. *)

            DEC (SrcPtr, count+1);
            token.TValue := 0;
            FOR j := 1 TO count DO
                ch := CAP (SrcBuf[SrcPtr]);
                INC (SrcPtr);
                IF ch IN Digits THEN
                    token.TValue := Add16 (radix*token.TValue, ORD(ch) - ORD('0'));
                ELSE
                    token.TValue := Add16 (radix*token.TValue, ORD(ch) - ORD('A') + 10);
                END (*IF*);
            END (*FOR*);

            (* Skip the trailing radix indicator. *)

            IF SrcBuf[SrcPtr] IN CharSet {'#', 'Q', '.', 'H'} THEN
                INC (SrcPtr);
            END (*IF*);
            ch := '9';       (* our internal code for number *)

        (* Check for quoted character. *)

        ELSIF ch = "'" THEN
            ch := SrcBuf[SrcPtr];
            INC (SrcPtr);
            token.TValue := ORD(ch);
            ch := '9';
            IF SrcBuf[SrcPtr] = "'" THEN
                INC (SrcPtr);
            ELSE
                ErrMes("'");
            END (*IF*);
        END (*IF*);

        (* All done, return the token and store back the source pointer. *)

        token.TCode := ch;

    END scan;

(************************************************************************)

PROCEDURE CkEol;

    (* Checks that there's nothing left (except comments) on the source line. *)

    BEGIN
        IF token.TCode <> Nul THEN
            ErrMes ('T');
            token.TCode := Nul;
        END (*IF*);
    END CkEol;

(************************************************************************)
(*               LOOKING UP THE PERMANENT SYMBOL TABLE                  *)
(************************************************************************)

PROCEDURE Compare6 (first: SixChar;  VAR (*IN*) second: SixChar): INTEGER;

    (* Returns <0 if first=second, =0 if first=second, >0 if first>second. *)

    VAR j: [0..5];

    BEGIN
        j := 0;
        LOOP
            IF first[j] > second[j] THEN RETURN +1
            ELSIF first[j] < second[j] THEN RETURN -1
            ELSIF j = 5 THEN RETURN 0
            ELSE INC(j);
            END (*IF*);
        END (*LOOP*);
    END Compare6;

(************************************************************************)

PROCEDURE LookUp (VAR (*OUT*) opcode: CARD8;  VAR (*OUT*) class: INTEGER);

    (* Looks up the current symbol in the permanent symbol table. *)
    (* If no match, a class of 0 is returned.                     *)

    VAR bottom, top, middle, length: CARDINAL;
        found: BOOLEAN;
        symbol: SixChar;

    BEGIN
        found := FALSE;
        class := 0;             (* Default if mnemonic not found *)
        bottom := 0;
        top := NumberOfMnemonics - 1;

        IF (token.TCode = 'A') AND (token.TName.length <= 6) THEN

            (* Pad the string with spaces. *)

            length := StringValue (token.TName, symbol);
            FOR middle := 0 TO length - 1 DO
                symbol[middle] := CAP(symbol[middle]);
            END (*FOR*);
            FOR middle := length TO 5 DO
                symbol[middle] := ' ';
            END (*FOR*);

            (* Binary search. *)

            WHILE bottom < top DO
                middle := (bottom + top) DIV 2;
                IF Compare6 (OpCodes[middle].mnem, symbol) < 0 THEN
                    bottom := middle + 1;
                ELSE
                    top := middle;
                END (*IF*);
            END (*WHILE*);

            found := (bottom = top) AND (Compare6 (OpCodes[bottom].mnem, symbol) = 0);

        END (*IF*);

        IF found THEN
            opcode := OpCodes[bottom].i_code;
            class := OpCodes[bottom].i_class;

            (* Update token. *)

            IF class = -3 THEN       (* .ASCII *)
                skipblank();
            ELSE
                scan();
            END (*IF*);
        END (*IF*);

    END LookUp;

(************************************************************************)
(*                        BINARY OUTPUT                                 *)
(************************************************************************)

PROCEDURE CodeOut (opcode: CARD8;  place: CARDINAL;  word_flag: BOOLEAN;
                              psect: psecttype);

    (* Puts code out to the listing and object files,        *)
    (* also updates location counter.                        *)

    BEGIN
        IF pass > 1 THEN
            PutObjectCode (opcode, place, word_flag, psect);
        END (*IF*);
        IncrementLocationCounter;
    END CodeOut;

(************************************************************************)
(*                          EXPRESSIONS                                 *)
(************************************************************************)

PROCEDURE expr (VAR (*OUT*) result: CARD16;
                VAR (*OUT*) psect: psecttype;
                VAR (*OUT*) external_symbol: String);   FORWARD;

(************************************************************************)

PROCEDURE primary (VAR (*OUT*) result: CARD16;
                VAR (*OUT*) psect: psecttype;
                VAR (*OUT*) external_symbol: String);

    (* Evaluates one primary element of an expression.  *)

    VAR flag, High, sym_defined, sym_equated: BOOLEAN;
        dummy: CARDINAL;

    BEGIN
        IF token.TCode = 'A' THEN       (* identifier *)

            flag := FALSE;

            IF StringIsDot (token.TName) THEN

                ReadLocationCounter (result, psect);
                flag := TRUE;
                scan;

            ELSIF token.LookAhead = '(' THEN

                (* check for H(expr) or L(expr).  *)

                High := FALSE;
                IF StringMatch (token.TName, "H") THEN
                    flag := TRUE;  High := TRUE;
                ELSIF StringMatch (token.TName, "L") THEN
                    flag := TRUE;
                END (*IF*);
                IF flag THEN
                    scan;  scan;
                    expr (result, psect, external_symbol);
                    IF psect <> abs_psect THEN
                        ErrMes ('X');  psect := abs_psect;
                    END (*IF*);
                    IF High THEN
                        result := result DIV 256;
                    END (*IF*);
                    IF token.TCode = ')' THEN
                        scan;
                    ELSE
                        ErrMes(')');
                    END (*IF*);
                    result := result MOD 256;
                END (*IF*);
            END (*IF*);

            IF NOT flag THEN
                getsym (dummy, token.TName, result,
                               sym_defined, sym_equated, psect);
                IF NOT sym_defined THEN
                    ErrMes('U');
                END (*IF*);
                scan;
            END (*IF*);

        (* That's the end of the alphanumeric case. *)

        ELSIF token.TCode = '9' THEN
            result := token.TValue;
            psect := abs_psect;
            scan;
        ELSE
            ErrMes ('Q');
            result := 0;
            psect := abs_psect;
        END (*IF*);

    END primary;

(************************************************************************)

PROCEDURE factor (VAR (*OUT*) result: CARD16;
                  VAR (*OUT*) psect: psecttype;
                  VAR (*OUT*) external_symbol: String);

    (* Evaluates one factor of an expression. *)

    BEGIN

        IF token.TCode = '(' THEN
            scan();
            expr(result, psect, external_symbol);
            IF token.TCode = ')' THEN
                scan();
            ELSE
                ErrMes(')');
            END (*IF*);
        ELSE
            primary (result, psect, external_symbol);
        END (*IF*);

    END factor;

(************************************************************************)

PROCEDURE term (VAR (*OUT*) result: CARD16;
                VAR (*OUT*) psect: psecttype;
                VAR (*OUT*) external_symbol: String);

    (* Evaluates one term of an expression. *)

    VAR op: CHAR;  newfactor: CARD16;
        newpsect: psecttype;  newsymbol: String;

    BEGIN

        (* Pick up first factor.         *)

        factor (result, psect, external_symbol);

        (* Now pick up all remaining factors. *)

        REPEAT
            op := token.TCode;
            IF (op = '*') OR (op = '/') THEN
                scan;
                factor (newfactor, newpsect, newsymbol);
                IF (psect <> abs_psect) OR (newpsect <> abs_psect) THEN
                    ErrMes('X');
                    result := 0;
                END (*IF*);
                psect := abs_psect;
            ELSE
                op := ' ';  newfactor := 0;
            END (*IF*);

            IF op = '*' THEN
                result := result * newfactor;
            ELSIF op = '/' THEN
                result := result DIV newfactor;
            END (*IF*);

        UNTIL op = ' ';

    END term;

(************************************************************************)

PROCEDURE expr (VAR (*OUT*) result: CARD16;
                VAR (*OUT*) psect: psecttype;
                VAR (*OUT*) external_symbol: String);

    (* Evaluates an expression in the source line. *)

    VAR op: CHAR;  newterm, swap: CARD16;
        newpsect: psecttype;  newsymbol: String;

    BEGIN

        (* Pick up first term, or assume it is zero in   *)
        (* the case of unary plus or unary minus.        *)

        IF (token.TCode = '+') OR (token.TCode = '-') THEN
            result := 0;
            psect := abs_psect;
        ELSE
            term (result, psect, external_symbol);
        END (*IF*);

        (* Now pick up all remaining terms. *)

        REPEAT
            op := token.TCode;
            IF (op = '+') OR (op = '-') THEN
                scan;
                term (newterm, newpsect, newsymbol);
            ELSE
                op := ' ';  newterm := 0;  newpsect := abs_psect;
            END (*IF*);

            IF op = '-' THEN
                IF newpsect = abs_psect THEN
                    newterm := Sub16 (0, newterm);
                    op := '+';
                ELSIF (newpsect = rel_psect) AND (psect = rel_psect) THEN
                    result := Sub16 (result, newterm);
                    psect := abs_psect;
                ELSE
                    ErrMes('X');
                END (*IF*);

            END (*IF*);

            IF op = '+' THEN
                 IF psect = abs_psect THEN
                     swap := result;
                     result := newterm;
                     newterm := swap;
                     external_symbol := newsymbol;
                     psect := newpsect;
                     newpsect := abs_psect;
                 END (*IF*);

                 IF newpsect <> abs_psect THEN
                     ErrMes('X');
                 END (*IF*);

                 result := Add16 (result, newterm);

             END (*IF*);

        UNTIL op = ' ';

    END expr;

(************************************************************************)

PROCEDURE expr8(): CARD8;

    (* Like expr, but checks that the answer is absolute     *)
    (* and only 8 bits long.                                 *)

    VAR answer: CARD16;  psect: psecttype;  symbol: String;

    BEGIN
        expr (answer, psect, symbol);
        IF psect <> abs_psect THEN
            ErrMes('V');
        ELSIF answer > 255 THEN
            ErrMes('V');
        END (*IF*);
        RETURN LowByte (answer);
    END expr8;

(************************************************************************)
(*                      PARSING/TRANSLATION PROCEDURES                  *)
(************************************************************************)

PROCEDURE Labels;

    (* Handles labels and symbol declarations. *)

    VAR nomore, def, equ: BOOLEAN;
        LHSname, external_name: String;
        expr_val: CARD16;  symptr: CARDINAL;
        psect: psecttype;

    BEGIN

        REPEAT

            nomore := TRUE;

            (* If end of line reached, get a new one. *)

            IF token.TCode = Nul THEN
                IF pass > 1 THEN ListTheLine (SrcBuf) END (*IF*);
                scan();
                nomore := FALSE;

            ELSIF token.TCode = 'A' THEN

                (* Recall that token.LookAhead holds a lookahead *)
                (* symbol.                                       *)

                IF token.LookAhead = ':' THEN

                    (* Label found. *)

                    ReadLocationCounter (expr_val, psect);
                    PutSym (token.TName, expr_val, FALSE, psect);
                    scan();  scan();
                    nomore := FALSE;

                ELSIF token.LookAhead = '=' THEN

                    (* assignment *)

                    LHSname := token.TName;
                    def := StringIsDot (LHSname);
                    IF NOT def THEN

                        (* The following call to getsym is only to       *)
                        (* ensure that the symbol is put into the        *)
                        (* symbol table in case it wasn't already        *)
                        (* there.  Therefore, most of the parameters     *)
                        (* are dummies.                                  *)

                        getsym (symptr, LHSname, expr_val, def, equ, psect);
                        def := FALSE;

                    END (*IF*);
                    scan();  scan();
                    expr (expr_val, psect, external_name);
                    IF def THEN
                        SetLocationCounter (expr_val, psect);
                    ELSE
                        PutSym (LHSname, expr_val, TRUE, psect);
                    END (*IF*);
                    nomore := FALSE;
                    CkEol();

                END (*IF*);
            END (*IF*);

        UNTIL nomore OR EndFlag;

    END Labels;

(************************************************************************)

PROCEDURE RegName(): CARDINAL;

    (* Looks for a register name, returns a register         *)
    (* number, i.e. 0 for B, 1 for C, ... , 7 for A.         *)

    VAR result: CARDINAL;  ch: ARRAY [0..0] OF CHAR;

    BEGIN
        (* Check that we have a one-letter identifier *)

        IF (token.TCode = 'A') AND (StringValue (token.TName, ch) = 1) THEN

            (* Search the list of register names *)

            result := 0;
            WHILE (result < 8) AND (ch[0] <> RegisterList[result]) DO
                INC (result);
            END (*WHILE*);
        ELSE
            result := 8;
        END (*IF*);

        IF result < 8 THEN
            scan();
            RETURN result;
        ELSE
            ErrMes('R');
            RETURN 0;
        END (*IF*);

    END RegName;

(************************************************************************)

PROCEDURE DRegName (option: CARDINAL): CARDINAL;

    (* Looks for a double register name, i.e. BC, DE, HL, AF, or SP.    *)
    (* options are interpreted as follows:                              *)
    (*     option = 5: AF illegal                                       *)
    (*     option = 6: SP illegal                                       *)
    (*     option = 7: both AF and SP illegal                           *)
    (* Sets result = 0 for BC, 16 for DE, 32 for HL, 48 for AF or SP.   *)

    VAR result: CARDINAL;  ch: ARRAY [0..1] OF CHAR;

    BEGIN
        (* Check that we have a two-letter identifier *)

        IF (token.TCode = 'A') AND (StringValue (token.TName, ch) = 2) THEN

            (* Search the list of register names for a match on *)
            (* the first character.                             *)

            result := 0;
            WHILE (result < 10) AND (ch[0] <> RegisterList[result]) DO
                INC (result);
            END (*WHILE*);

            (* Now check the second character. *)

            IF (result < 10) AND (ch[1] <> RegisterList[result+1]) THEN
                result := 8;
            END (*IF*);

        ELSE
            result := 8;
        END (*IF*);

        (* Check to see whether what we found is consistent with the option. *)

        IF ODD(result) THEN

            (* If result is odd, we either have an error, or *)
            (* the symbol was AF or SP.  Check these out.    *)
            (* (Will have 7 for AF, 9 for SP).               *)

            IF ((option = 5) AND (result = 9))
                             OR ((option = 6) AND (result = 7)) THEN
                result := 6;
            ELSE
                result := 8;
            END (*IF*);

        ELSIF result > 4 THEN

            (* Reject the 'names' MA, FS *)

            result := 8;

        END (*IF*);

        IF result < 8 THEN
            scan();
            RETURN 8*result;
        ELSE
            ErrMes('D');
            RETURN 0;
        END (*IF*);

    END DRegName;

(************************************************************************)

PROCEDURE Operands (opcode: CARD8;  class: CARDINAL);

    (* Procedure to handle the operand fields (including the case of    *)
    (* instructions which have no operands), and finish processing of   *)
    (* the source line.                                                 *)

    VAR bufptr: CARDINAL;  x: CARD8;  value: CARD16;
        psect: psecttype;
        symbol: String;

    BEGIN

        (* Put the location counter into the listing buffer. *)

        PrtLC;
        bufptr := 1;

        (* Now the actual operand processing: *)

        CASE class OF

          |  1:         (* no operands, nothing to do *)

          |  2:         (* single destination register, e.g. dcr *)
                INC (opcode, CARD8(8*RegName()));

          |  3:         (* rst *)
                x := expr8();
                IF x > 7 THEN
                    ErrMes('V');
                END (*IF*);
                INC (opcode, 8*(x MOD 8));

          |  4:         (* mov *)
                INC (opcode, CARD8(8*RegName()));
                IF token.TCode = ',' THEN
                    scan();
                ELSE
                    ErrMes (',');
                END (*IF*);
                INC (opcode, CARD8(RegName()));
                IF opcode = 118 THEN
                    ErrMes('H');
                END (*IF*);

          |  5..7:      (* double register operand. Class 5 is dad,   *)
                        (* dcx, inx. Class 6 is pop, push. Class 7 is *)
                        (* ldax, stax.                                *)
                INC (opcode, CARD8(DRegName(class)));

          |  8:         (* mvi *)
                INC (opcode, CARD8(8*RegName()));
                CodeOut (opcode, 1, FALSE, abs_psect);
                bufptr := 2;
                IF token.TCode = ',' THEN
                    scan();
                ELSE
                    ErrMes(',');
                END (*IF*);
                opcode := expr8();

          |  9, 10:                (* one immediate operand, e.g. adi or in *)
                CodeOut (opcode, 1, FALSE, abs_psect);
                bufptr := 2;
                opcode := expr8();

          | 11:                (* two-byte address field, e.g. jmp *)
                CodeOut (opcode, 1, FALSE, abs_psect);
                expr (value, psect, symbol);
                CodeOut (LowByte(value), 2, TRUE, psect);
                bufptr := 3;
                opcode := HighByte(value);

          | 12:                (* lxi *)
                INC (opcode, CARD8(DRegName(5)));
                CodeOut (opcode, 1, FALSE, abs_psect);
                IF token.TCode = ',' THEN
                    scan();
                ELSE
                    ErrMes(',');
                END (*IF*);
                expr (value, psect, symbol);
                CodeOut (LowByte(value), 2, TRUE, psect);
                bufptr := 3;
                opcode := HighByte(value);

          | 13:                (* single source register, e.g. add *)
                INC (opcode, CARD8(RegName()));

        ELSE
                WrStr ("Error in Operands.");  WrLn;
        END (*CASE*);

        (* Put out the last byte of the instruction. *)

        CodeOut (opcode, bufptr, FALSE, abs_psect);

    END Operands;

(************************************************************************)

PROCEDURE Pseudo (psenum: CARDINAL);

    (* Handles all assembler directives except '='. *)

    (********************************************************************)

    PROCEDURE newline;

        (* Moves to new listing line.  *)

        BEGIN
            IF pass > 1 THEN ListTheLine(SrcBuf) END (*IF*);
            ClearPreamble();
            SrcBuf[0] := CHR(0);
            PrtLC;
        END newline;

    (********************************************************************)

    VAR count: CARDINAL;  numval: CARD16;
        delimiter, ch: CHAR;
        psect: psecttype;
        symbol: String;

    BEGIN
        (* psenum = 0 means implicit .byte,     *)
        (* psenum = 1 means explicit .byte.     *)
        (* Reduce these to a uniform case.      *)

        IF psenum = 0 THEN psenum := 1; END (*IF*);

        IF psenum < 4 THEN
            PrtLC;
        END (*IF*);

        (* Now handle each directive separately.  *)

        count := 1;
        CASE psenum OF

          |  1:         (* .byte *)
                REPEAT
                    IF count = 4 THEN
                        newline();  count := 1;
                    END (*IF*);

                    CodeOut (expr8(), count, FALSE, abs_psect);

                    IF token.TCode = ',' THEN
                        INC (count);
                        scan();
                    ELSE
                        count := 0;
                    END (*IF*);

                UNTIL count = 0;

          |  2:         (* .word *)
                REPEAT

                    expr (numval, psect, symbol);
                    CodeOut (LowByte(numval), 1, TRUE, psect);
                    CodeOut (HighByte(numval), 2, FALSE, abs_psect);
                    INC (count);

                    IF token.TCode = ',' THEN
                        scan();  newline();
                    ELSE
                        count := 0;
                    END (*IF*);

                UNTIL count = 0;

          |  3:         (* .ascii *)
                delimiter := SrcBuf[SrcPtr];
                INC (SrcPtr);
                REPEAT
                    ch := SrcBuf[SrcPtr];
                    IF ch = CHR(0) THEN
                        ch := delimiter;
                        ErrMes('A');
                    ELSE
                        INC (SrcPtr);
                    END (*IF*);

                    IF ch = delimiter THEN
                        scan;  count := 0;
                    ELSE
                        IF count = 4 THEN
                            newline();  count := 1;
                        END (*IF*);
                        CodeOut (CARD8(ch), count, FALSE, abs_psect);
                        INC (count);
                    END (*IF*);

                UNTIL count = 0;

          |  4:         (* .page *)
                ReadLocationCounter (numval, psect);
                numval := IAND (numval + 255, 0FF00H);
                SetLocationCounter (numval, psect);

          |  5:         (* .END *)
                EndFlag := TRUE;
                IF token.TCode <> CHR(0) THEN
                    StartAddress.Supplied := TRUE;
                    expr (StartAddress.val, StartAddress.psect, symbol);
                    IF StartAddress.psect = external_symbol THEN
                        ErrMes('X');
                    END (*IF*);
                END (*IF*);

          |  6:         (* .abs  *)
                SetPsect (abs_psect);

          |  7:         (* .rel  *)
                SetPsect (rel_psect);

          |  8:         (* .globl        *)
                LOOP
                    IF token.TCode = 'A' THEN
                        IF pass = 1 THEN
                            PutSym (token.TName, 0, TRUE, external_symbol);
                        END (*IF*);
                        scan;
                    ELSE
                        ErrMes('G');
                    END (*IF*);

                    IF token.TCode = ',' THEN
                        scan();
                    ELSE
                        EXIT (*LOOP*);
                    END (*IF*);
                END (*LOOP*);
        ELSE
                WrStr ("Unknown assembler directive");
                WrLn;

        END (*CASE*);

    END Pseudo;

(************************************************************************)
(*                          THE TOP LEVEL OF THE ASSEMBLER              *)
(************************************************************************)

PROCEDURE OneLine;

    (* Assembles a single source line.  *)

    VAR opcode: CARD8;  class: INTEGER;

    BEGIN
        scan;
        Labels;               (* Handle labels, symbol declarations *)

        (* We have now handled all labels (if any).  token.TName should  *)
        (* be holding an instruction mnemonic or pseudo-op.              *)

        LookUp (opcode, class);
        IF class > 0 THEN
            Operands (opcode, class);
        ELSIF NOT EndFlag THEN
            Pseudo (ABS(class));
        END (*IF*);
        CkEol();
        IF pass > 1 THEN
            ListTheLine (SrcBuf);
        END (*IF*);
    END OneLine;

(************************************************************************)

PROCEDURE OnePass;

    (* One complete pass of the assembly.  *)

    BEGIN
        EndFlag := FALSE;
        ClearLocationCounter;
        InitScanner;
        REPEAT
            OneLine;
        UNTIL EndFlag;
        FIO.Close (srchandle);
    END OnePass;

(************************************************************************)

PROCEDURE Assemble;

    VAR code, checksum: CARD8;
        LC: CARD16;  psect: psecttype;

    BEGIN

        pass := 1;
        OnePass;

        (* End of pass 1.  Print the symbol table, and put an    *)
        (* "} GSD" record out to the object file.                *)

        OpenOutputFiles (TRUE, TRUE);
        PrintSymbolTable;
        IF obj_option THEN
            ReadLocationCounter (LC, psect);
            checksum := 0;
            putobject (5, checksum);
            putobject (2, checksum);
            putobject (LowByte(LC), checksum);
            putobject (HighByte(LC), checksum);
            putobject (checksum, checksum);
        END (*IF*);

        (* Start pass 2.         *)

        INC (pass);
        OnePass;
        IF obj_option THEN
            FlushBuffer;

            (* Write the "end module" record. *)

            checksum := 0;
            code := 1;
            IF StartAddress.psect = rel_psect THEN
                code := 129;
            END (*IF*);
            putobject (code, checksum);
            IF StartAddress.Supplied THEN
                putobject (2, checksum);
                putobject (LowByte (StartAddress.val), checksum);
                code := HighByte (StartAddress.val);
            ELSE
                code := 0;
            END (*IF*);
            putobject (code, checksum);
            putobject (checksum, checksum);

        END (*IF*);

    END Assemble;

(************************************************************************)
(*                              MAIN PROGRAM                            *)
(************************************************************************)

PROCEDURE GetArguments;

    (* Picks up program arguments from the command line. *)

    TYPE CharNumber = [0..79];

    VAR Options: ARRAY CharNumber OF CHAR;
        j, k: CARDINAL;

    BEGIN
        IF ParamCount() = 0 THEN
            SourceName := "";
        ELSE
            ParamStr (Options, 1);
            j := 0;
            WHILE (j <= MAX(CharNumber)) AND (Options[j] = Space) DO
                INC (j);
            END (*WHILE*);

            (* Read in a file name. *)

            k := 0;
            WHILE (j <= MAX(CharNumber)) AND (Options[j] <> Nul)
                                         AND (Options[j] <> Space) DO
                SourceName[k] := Options[j];
                INC (j);  INC (k);
            END (*WHILE*);
            SourceName[k] := Nul;

            (* I'll implement the other options at a later stage. *)

        END (*IF*);

    END GetArguments;

(************************************************************************)

PROCEDURE RunTheProgram;

    VAR ErrCount: CARDINAL;

    BEGIN
        list_option := TRUE;
        obj_option := FALSE; (* set this for binary output option *)

        WrLn;
        WrStr (" Department of Electrical and Computer Engineering");
        WrLn;
        WrStr ("                University of Newcastle");
        WrLn;
        WrStr ("       ******* 8085/8080 Cross Assembler *******");
        WrLn;  WrLn;

        GetArguments;
        IF SourceName[0] = Nul THEN
            WrStr ("You have to supply a source file name.");
            WrLn;
        ELSE
            SetOutputFileNames (SourceName);

            StartAddress.Supplied := FALSE;
            StartAddress.psect := abs_psect;
            Assemble;
            ErrCount := CloseOutputFiles();
            IF ErrCount = 0 THEN
                WrStr (" No errors.");
            ELSE
                WrCard (ErrCount, 6);  WrStr (" errors.");
            END (*IF*);
            WrLn;
        END (*IF*);

    END RunTheProgram;

(************************************************************************)

BEGIN
    RunTheProgram;
END as85.
