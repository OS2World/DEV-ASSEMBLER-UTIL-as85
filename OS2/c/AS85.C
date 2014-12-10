/****************************************************/
/****						****/
/****		A S 8 5 . C    			****/
/****						****/
/****************************************************/

/* ================================================================ */
/* */
/* CROSS-ASSEMBLER FOR 8085.					 */
/* */
/* This is a C translation of a program written in Pascal	 */
/* but translated from a program originally written in SGL.	 */
/* */
/* Programmer:		V. Holmberg			 */
/* Date started:		22 August 91			 */
/* Lasted Modified:					 */
/* */
/* Modifications:						 */
/* */
/* Left over from Pascal translation			 */
/* */
/* Still to be done:					 */
/* */
/* Cleaner approach to string handling		 */
/* Get '.' out of symbol table			 */
/* */
/* ================================================================ */

/* ======================================================================== */
/* REMARK: THIS PROGRAM DEVIATES SOMEWHAT FROM STANDARD RECOMMENDED	 */
/* PRACTICE, FOR EXAMPLE IN THAT I USE A LOT OF GLOBAL VARIABLES WHERE	 */
/* LOCAL STATIC VARIABLES WOULD BE MORE APPROPRIATE.  THE REASON IN	 */
/* THE ORIGINAL SGL PROGRAM WAS THAT THIS WOULD LATER SIMPLIFY THE	 */
/* TASK OF TRANSLATING THE PROGRAM INTO 8080 ASSEMBLY LANGUAGE, AND	 */
/* PUTTING IT INTO ROM.  NOW THE REASON IS THAT IT WAS EASIER TO	 */
/* CONVERT THE ORIGINAL PROGRAM INTO PASCAL THAN TO WRITE A NEW	 */
/* VERSION FROM SCRATCH.						 */
/* ======================================================================== */


#include <stdio.h>
#include <mem.h>		/* Wylie */
#include <ctype.h>
#include <string.h>		/* Wylie */
#include <stdlib.h>		/* Wylie */

void ClearPreamble(void);	/* Wylie */
void LineIn(void);   		/* Wylie */
void skipblank(void);     	/* Wylie */
void ListTheLine(void);		/* Wylie */
void FlushBuffer(void);		/* Wylie */
void PrtLC(void);			/* Wylie */
void scan(void);			/* Wylie */
int RegName(void);			/* Wylie */
int DstName(void);			/* Wylie */
int expr8(void);			/* Wylie */
void CkEol(void);			/* Wylie */
void newline(void);			/* Wylie */
void Labels(void);			/* Wylie */
void InitScanner(void);		/* Wylie */
void OneLine(void);			/* Wylie */
void OnePass(void);			/* Wylie */
void PrintSymbolTable(void);	/* Wylie */
void Init_Permanent_Symbol_Table(void);	/* Wylie */
void InitBinout(void);		/* Wylie */
void Assemble(void);		/* Wylie */

#define EOS		'\0'
#define EOLN		'\n'
#define EOF		(-1)
#define TAB		'\t'
#define SPACE		' '
#define formfeed	012
#define true		1
#define false		0
#define byte		unsigned char
#define boolean		int


#define TraceFlag  		false
#define testlevel  		00	/* For debugging purposes.	 */
#define obj_line		32	/* line length for object file */
#define LineSize  		80
#define string_table_size   	3000	/* Size of character string table. */
#define sytsiz  		4000	/* Symbol table size		 */
#define max_mnemonics  		88	/* Permanent symbol table size.	 */
#define codebufferlimit  	10	/* Object code buffer size - 1	 */

/* ======================= */
/* typedefs 	 */
/* ======================= */

#define abs_psect      		0
#define rel_psect               1
#define external_symbol         2





typedef short   psecttype;

typedef char    twochar[3];
typedef char    fourchar[5];
typedef char    sixchar[7];
typedef char    eightchar[9];

typedef struct OpCodes_type {
	sixchar         mnem;
	int             i_code, i_class;
}               OpCodes_type;

typedef struct string {
	int             length;
	int             pointer;
}               string;

typedef struct Symbol_table_entry {
	string          name;
	boolean         defined_, equated;
	psecttype       sym_psect;
	int             symval;
}               Symbol_table_entry;

/* ======================= */
/* Variables	 */
/* ======================= */

/* list file option and object file option */

static boolean  list_option, obj_option, run_option;

/* Files. */

static FILE    *sourcefile, *listing;
static FILE    *object, *opfile;

/* Object code buffers.	 */

static struct {
	psecttype       ExpectedPsect;
	int             StartLC, ExpectedLC;
	byte            val[codebufferlimit + 1];
}               CodeBuffer;

static struct {
	byte            count;
	byte            val[codebufferlimit + 1];
}               RLDbuffer;

static struct {
	boolean         Supplied;
	psecttype       psect;
	int             val;
}               StartAddress;

/* Listing buffer.	 */

static struct {
	char            err;	/* Error code		 */
	fourchar        LC;	/* Location counter (hex)	 */
	char            LCflag;	/* Flag for LC relative.	 */
	twochar         code[3];/* Hex object code	 */
	char            codeflag;	/* Flag relocation of code.	 */
}               ListBuffer;

/* Source buffer.	 */

static char     SrcBuf[81];
static int      SrcPtr;

/* Scanner variables. */

static struct {
	char            TCode, LookAhead;
	struct string   TName;
	int             TValue;
}               token;

/* Location counter	 */

static psecttype current_psect;
static int      LocCtr[external_symbol];	/* this is the same as
						 * LocCtr[psecttype] in
						 * pascal */

/* Pass counter, end-of-pass flag, error count. */

static int      pass, ErrCount;
static boolean  EndFlag;

/* Trace level. */

static int      TraceLevel;

/* Permanent symbol table. */

static int      Number_of_mnemonics;
static OpCodes_type OpCodes[max_mnemonics + 1];
static char     register_list[10];

/* Symbol table. */

static struct {
	int             nextfree;
	char            val[string_table_size + 1];
}               string_table;

static int      nsyms;
static Symbol_table_entry SymTbl[sytsiz + 1];

/* Opcode file line length */

static int	op_line_length = 0;

int             BYTE_WRITTEN;

/* =================================================================== */
/* =================================================================== */

void            expr();

/* =================================================================== */


/* =================================================================== */
/* ====								=== */
/* ====			TESTING TOOLS				=== */
/* ====								=== */
/* =================================================================== */

void In_Trace(eightchar procname)
{
	TraceLevel++;
	printf("%*c - Entering %.8s\n", (int) (2 * TraceLevel), ' ', procname);
}

/* =================================================================== */

void
OutTrace(eightchar procname)
{
	printf("%*c - Leaving %.8s\n", (int) (2 * TraceLevel), ' ', procname);
	TraceLevel--;
}

/* =================================================================== */
/* ====								=== */
/* ====		MISCELLANEOUS UTILITY ROUTINES			=== */
/* ====								=== */
/* =================================================================== */

byte
XORR(byte a, byte b)
{

	/* Computes the exclusive OR of its two arguments.	 */

	byte            answer, j;
	int             mask;

	answer = 0;
	mask = 1;
	for (j = 1; j <= 8; j++) {
		if ((a & 1) != (b & 1))
			answer += mask;
		a /= 2;
		b /= 2;
		mask *= 2;
	}
	return answer;
}

/* =================================================================== */

char
hex1(int number)
/* Converts the low-order 4 bits of number to a hexadecimal character */

{
	number = number & 15;
	if (number < 10)
		return ((char) (number + '0'));	/* return number - ord('0') 	 */
	else
		return ((char) (number + 'A' - 10));	/* return number - 10 +
							 * ord('A') */

}

/* =================================================================== */

void
hex_(int number, twochar * chars)
/* Converts the low-order 8 bits of number to hexadecimal,	 */
/* answer goes into chars with most significant digit in	 */
/* first byte, least significant digit in second byte.	 */

{
	number = number & 255;
	(*chars)[0] = hex1(number / 16);
	(*chars)[1] = hex1(number & 15);
}

/* =================================================================== */

byte
shr8(int x)
/* Shifts a binary two's complement number 8 bits right.	 */

{
	return (x >> 8);	/* ((x - (x mod 256)) div 256) mod 256 */
}

/* =================================================================== */
/* ====								=== */
/* ====			OUTPUT ROUTINES				=== */
/* ====								=== */
/* =================================================================== */

void
PrtHex(int number)
/* Prints number in hexadecimal. */


{
	twochar         partanswer;

	if (list_option) {
		hex_(shr8(number), &partanswer);
		fprintf(listing, "%.2s", partanswer);
		hex_(number & 255, &partanswer);
		fprintf(listing, "%.2s", partanswer);
	}
}

/* =================================================================== */

void
ClearPreamble()
/* Resets the listing buffer. */
{

	byte            j;

	ListBuffer.err = ' ';	/* Clear error code	 */
	memcpy(ListBuffer.LC, "    ", sizeof(fourchar));	/* Clear location
								 * counter part	 */
	ListBuffer.LC[4] = '\0';
	ListBuffer.LCflag = ' ';
	for (j = 0; j <= 2; j++) {	/* Clear code part	 */
		memcpy(ListBuffer.code[j], "  ", sizeof(twochar));
		ListBuffer.code[j][2] = '\0';
	}
	ListBuffer.codeflag = ' ';
}

/* =================================================================== */

void
ErrMes(char ErrorCode)
/* Error message routine.  Will only log the first error on each line. */

{
	if (ListBuffer.err == ' ') {
		ListBuffer.err = ErrorCode;
		ErrCount++;

		if (testlevel > 90)
			printf("%*c - Visting ErrMes\n", (int) (2 * (TraceLevel + 1)), ' ');

	}
}

/* =================================================================== */
/* ====								=== */
/* ====			INPUT ROUTINES				=== */
/* ====								=== */
/* =================================================================== */

/*
 * Check if at end of file, using Pascal "eof" semantics.  End-of-file for
 * stdin is broken; remove the special case for it to be broken in a
 * different way. 
 */

int
P_eof(FILE * f)
{
	register int    ch;

	if (feof(f))
		return 1;
	if (f == stdin)
		return 0;	/* not safe to look-ahead on the keyboard! */
	ch = getc(f);
	if (ch == EOF)
		return 1;
	ungetc(ch, f);
	return 0;
}

/* =================================================================== */

/* Check if at end of line (or end of entire file). */

int
P_eoln(FILE * f)
{
	register int    ch;

	ch = getc(f);
	if (ch == EOF)
		return 1;
	ungetc(ch, f);
	return (ch == '\n');
}

/* =================================================================== */

void
skipblank()
/* Updates the buffer pointer srcptr to skip spaces	 */
/* and tabs.						 */

{
	while ((SrcBuf[SrcPtr - 1] == SPACE) || (SrcBuf[SrcPtr - 1] == TAB))
		SrcPtr++;
}

/* =================================================================== */

boolean
alpha(char ch)
{
	return (isalpha(ch) || (ch == '.') || (ch == '$') || (ch == '_'));
}

/* =================================================================== */

char
uppercase(char ch)
/* Converts lower case to upper case, leaves other characters unchanged. */

{
	if (islower(ch))
		return toupper(ch);
	else
		return ch;
}

/* =================================================================== */

int
numeric(char ch)
/* Converts one hexadecimal character to integer, but sets	 */
/* result = -1 for illegal character.			 */

{
	if (isdigit(ch))
		return (ch - '0');
	else if ((ch >= 'A') && (ch <= 'F'))
		return (ch - 'A' + 10);
	else
		return -1;
}

/* =================================================================== */

void
LineIn()
/* Procedure to get in new source line. */

{

	int             BufPtr;
	char            ch;

	/* Clear the error code, etc., part of the buffer. */

	ClearPreamble();

	/* Now read the source line, echoing it and checking for	 */
	/* line too long.					 */

	BufPtr = 1;
	if (P_eof(sourcefile)) {/* Premature end of file */
		ErrMes('E');
		SrcBuf[0] = EOS;
		EndFlag = true;
	} else {
		while (!P_eoln(sourcefile)) {
			ch = getc(sourcefile);
			if (ch == '\n')
				ch = ' ';
			SrcBuf[BufPtr - 1] = ch;
			if (BufPtr == LineSize)
				ErrMes('L');
			else
				BufPtr++;
		}
		SrcBuf[BufPtr - 1] = EOS;
		fscanf(sourcefile, "%*[^\n]");
		getc(sourcefile);
	}
}

/* =================================================================== */

void
CkEol()
/* Makes sure that we are at end of line. */

{
	if (token.TCode != EOS) {
		ErrMes('T');
		token.TCode = EOS;
	}
}

/* =================================================================== */

int
MulAdd(int radix, int numval, char ch)
/* Computes radix*numval + numeric(ch), with the restriction	 */
/* that radix may only be 2, 8, 10, or 16.				 */
/* Special case: radix == 0 really means radix == 16.		 */


{
	int             ans, addcon;

	ans = 2 * numval;
	addcon = numeric(ch);
	if (radix == 10)
		addcon += ans;

	/* Now must multiply by 1, 4, 4, or 8.  */

	if (radix != 2)
		ans *= 4;
	if ((radix == 0) || (radix == 16))   /* Wylie - changed '=' to '==' */
		ans *= 2;
	ans += addcon;
	return ans;
}

/* =================================================================== */
/* ====								=== */
/* ====				SCANNER				=== */
/* ====								=== */
/* =================================================================== */

void
print_string(string sym_name)
{
	int             j;

	for (j = -1; j <= sym_name.length - 2; j++)
		putchar(string_table.val[sym_name.pointer + j]);
}

/* =================================================================== */

void
dump_string(string sym_name)
{
	printf("%12ld%12ld   '", sym_name.length, sym_name.pointer);
	print_string(sym_name);
	printf("'\n");
}

/* =================================================================== */

void
scan()
{

	int             TokPtr;
	char            ch;
	int             radix, count, j, place;

	/* If token == chr(0) (from the last scan), we	 */
	/* need to get in a new line.			 */

	if (token.TCode == '\0') {
		LineIn();
		SrcPtr = 1;
	}
	/* Skip leading blanks.  Note that we don't skip blank lines,	 */
	/* since the routine responsible for listing will want to	 */
	/* know about them.						 */

	skipblank();
	TokPtr = SrcPtr;
	ch = SrcBuf[TokPtr - 1];
	TokPtr++;

	if (ch == ';')
		ch = '\0';

	/* Check for identifier.  If found, put the name into the string	 */
	/* table, and a pointer to it into token.TName.			 */

	else if (alpha(ch)) {
		count = 0;
		place = string_table.nextfree;
		token.TName.pointer = place;
		while (alpha(ch) || (numeric(ch) >= 0)) {
			count++;
			if (place >= string_table_size)
				ErrMes('O');
			else {
				string_table.val[place - 1] = uppercase(ch);
				place++;
			}
			ch = SrcBuf[TokPtr - 1];
			TokPtr++;
		}
		token.TName.length = count;
		ch = 'A';

		/* Skip trailing blanks, put a lookahead symbol	 */
		/* into LookAhead (for use by label and primary)	 */

		SrcPtr = TokPtr - 1;
		skipblank();
		TokPtr = SrcPtr;
		token.LookAhead = SrcBuf[TokPtr - 1];
		if ((token.LookAhead != ':') && (token.LookAhead != '=')
		    && (token.LookAhead != '('))
			token.LookAhead = ' ';
	} else if (ch == (char) formfeed)
		ch = '\0';

	/* Check for number.  note that because of the order in which	 */
	/* the checking is done, numbers may not start with A..F.	 */

	else if (numeric(ch) >= 0) {

		/* First, count the number of digits */

		count = 0;
		while (numeric(ch) >= 0) {
			count++;
			ch = SrcBuf[TokPtr - 1];
			TokPtr++;
		}
		TokPtr--;

		/* Now work out the radix  */

		radix = 0;	/* default is hexadecimal */
		if (ch == '#')
			radix = 2;
		else if (ch == 'Q')
			radix = 8;
		else if (ch == '.')
			radix = 10;
		else if (ch == 'H')
			radix = 16;

		/* Now go back and convert the number to binary. */

		TokPtr -= count;
		token.TValue = 0;
		for (j = 1; j <= count; j++) {
			ch = SrcBuf[TokPtr - 1];
			TokPtr++;
			token.TValue = MulAdd(radix, token.TValue, ch);
		}

		/* Skip the trailing radix indicator. */

		if (radix != 0)
			TokPtr++;
		ch = '9';	/* our internal code for number */
	}
	/* Check for quoted character. */

	else if (ch == '\'') {
		ch = SrcBuf[TokPtr - 1];
		TokPtr++;
		token.TValue = ch;
		ch = '9';
		if (SrcBuf[TokPtr - 1] == '\'')
			TokPtr++;
		else
			ErrMes('\'');
	}
	/* All done, return the token and store back the source pointer. */

	token.TCode = ch;
	SrcPtr = TokPtr;

	if (testlevel > 15) {
		printf("Now leaving scanner.  token is %c\n", token.TCode);
		if (token.TCode == 'A')
			dump_string(token.TName);
	}
	return;
}

/* =================================================================== */

void
InitScanner()
{
	token.TCode = '\0';
}

/* =================================================================== */
/* ====								=== */
/* ====			LISTING ROUTINES			=== */
/* ====								=== */
/* =================================================================== */

void
ListTheLine()
{
	int             j;

	if (list_option) {
		fprintf(listing, "%c %.4s%c", ListBuffer.err, ListBuffer.LC, ListBuffer.LCflag);
		fprintf(listing, "%.2s ", ListBuffer.code[0]);
		fprintf(listing, "%.2s ", ListBuffer.code[1]);
		fprintf(listing, "%.2s%1c", ListBuffer.code[2], ListBuffer.codeflag);
		j = 0;
		while (SrcBuf[j] != '\0') {
			fprintf(listing, "%c", SrcBuf[j]);
			j++;
		}
		putc('\n', listing);

		for ( j=0; j<3; j++){
			if ( ListBuffer.code[j][1] != ' ' ) {
				fprintf(opfile,"%.2s",ListBuffer.code[j]);
				op_line_length++;
			}
			if ( op_line_length >= 16 ) {
				fprintf(opfile, "\n");
				op_line_length = 0;
			}
		}
	}
	return;
}

/* =================================================================== */

void
PrtLC()
/* Puts the location counter (in hex) into the listing buffer. */


{
	int             j, currentLC;

	currentLC = LocCtr[current_psect];
	ListBuffer.LC[3] = hex1(currentLC);
	for (j = 2; j >= 0; j--) {
		currentLC /= 16;/* div 16 */
		ListBuffer.LC[j] = hex1(currentLC);
	}
	if (current_psect == rel_psect)
		ListBuffer.LCflag = '\'';
}

/* =================================================================== */

void
newline()
/* Moves to new listing line.  */

{
	if (pass > 1)
		ListTheLine();
	ClearPreamble();
	SrcBuf[0] = '\0';
	PrtLC();
}

/* =================================================================== */
/* ====								=== */
/* ====			BINARY OUTPUT				=== */
/* ====								=== */
/* =================================================================== */

/* local structure for putobject */
struct LOC_putobject {
	byte            value;
};

/* =================================================================== */

void
putobject(byte value_, byte * checksum)
/* Puts a byte out to the object file, and updates	 */
/* the checksum.						 */

{

	struct LOC_putobject V;

	V.value = value_;
	fwrite(&V.value, sizeof(byte), 1, object);
	BYTE_WRITTEN++;
	*checksum = XORR(*checksum, V.value);
}				/* of putobject */

/* =================================================================== */

void
FlushBuffer()
/* Sends the current contents of the binary output buffer	 */
/* to the object file.					 */

{				/* body of FlushBuffer */

	byte            checksum;
	int             j;

	if (TraceFlag)
		In_Trace("FlushBuf");

	if (CodeBuffer.StartLC != CodeBuffer.ExpectedLC) {

		/* Write the record header and byte count.	 */

		checksum = 0;
		if (CodeBuffer.ExpectedPsect == abs_psect)
			putobject(2, &checksum);
		else
			putobject(130, &checksum);
		putobject((CodeBuffer.ExpectedLC - CodeBuffer.StartLC + 2), &checksum);

		/* Then the load address.	 */

		putobject(CodeBuffer.StartLC & 255, &checksum);
		putobject(CodeBuffer.StartLC / 256, &checksum);

		/* Now the binary data.	 */

		for (j = 0; j < (CodeBuffer.ExpectedLC - CodeBuffer.StartLC); j++) {
			putobject(CodeBuffer.val[j], &checksum);
		}

		/* Finally, the checksum.	 */

		fwrite(&checksum, sizeof(byte), 1, object);

	}
	CodeBuffer.StartLC = LocCtr[current_psect];
	CodeBuffer.ExpectedLC = LocCtr[current_psect];
	CodeBuffer.ExpectedPsect = current_psect;

	/* Flush the RLD buffer.	 */

	if (RLDbuffer.count != 0) {

		/* Write the record header and byte count.	 */

		checksum = 0;
		putobject(3, &checksum);
		putobject(RLDbuffer.count, &checksum);

		/* Now the binary data.	 */

		for (j = 0; j < RLDbuffer.count; j++) {
			putobject(RLDbuffer.val[j], &checksum);
		}

		/* Finally, the checksum.	 */

		fwrite(&checksum, sizeof(byte), 1, object);
		RLDbuffer.count = 0;
	}
	if (TraceFlag)
		OutTrace("FlushBuf");
}				/* of FlushBuffer */

/* =================================================================== */

void
binout(byte value, boolean word_flag, psecttype psect, string symbol)
/* Puts a byte into the binary output buffer.  If necessary,	 */
/* flushes the output buffer before starting a new			 */
/* buffer-full.  If word_flag is true, this indicates that		 */
/* this is the first byte of a word.				 */


{
	boolean         new_record_needed;
	byte            j, offset, sub_record_kind, RLD_space_needed;

	if (TraceFlag)
		In_Trace("Binout  ");
	if (TraceFlag) {
		printf("LocCtr [%i], expected [%i], startLC [%i], value [%i] \n",
		       LocCtr[current_psect], CodeBuffer.ExpectedLC, CodeBuffer.StartLC, value);
	}
	/* Work out what sort of relocation record is needed.	 */

	sub_record_kind = 0;
	RLD_space_needed = 0;
	if (psect == rel_psect) {
		sub_record_kind = 1;
		RLD_space_needed = 2;
	} else if (psect == external_symbol) {
		sub_record_kind = 2;
		RLD_space_needed = 3 + symbol.length;
	}
	if ((word_flag) && (psect != abs_psect))
		sub_record_kind += 128;

	/* Work out whether a new record has to be started.	 */

	offset = LocCtr[current_psect] - CodeBuffer.StartLC;
	new_record_needed = (LocCtr[current_psect] != CodeBuffer.ExpectedLC)
		|| (current_psect != CodeBuffer.ExpectedPsect)
		|| (offset > codebufferlimit)
		|| (word_flag && (offset == codebufferlimit))
		|| (RLD_space_needed > (RLDbuffer.count + codebufferlimit));
	if (new_record_needed) {
		FlushBuffer();
		offset = 0;
	}
	if (TraceFlag) {
		printf("LocCtr [%i], expected [%i], startLC [%i], value [%i] \n",
		       LocCtr[current_psect], CodeBuffer.ExpectedLC, CodeBuffer.StartLC, value);
	}
	/* Put the new byte into the buffer.	 */

	CodeBuffer.val[offset] = value;
	CodeBuffer.ExpectedLC = LocCtr[current_psect] + 1;

	/* Put whatever is needed into the relocation buffer.	 */

	if (sub_record_kind != 0) {
		RLDbuffer.val[RLDbuffer.count] = sub_record_kind;
		RLDbuffer.count++;
		RLDbuffer.val[RLDbuffer.count] = offset;
		RLDbuffer.count++;
		if (psect == external_symbol) {
			RLDbuffer.val[RLDbuffer.count] = symbol.length;
			RLDbuffer.count++;
			for (j = -1; j <= (symbol.length - 2); j++) {
				RLDbuffer.val[RLDbuffer.count] =
					string_table.val[symbol.pointer + j];
				RLDbuffer.count++;
			}
		}
	}
	if (TraceFlag)
		OutTrace("Binout  ");
}

/* =================================================================== */

void
InitBinout()
/* Sets up the initial conditions for binary output.	 */

{
	CodeBuffer.ExpectedPsect = abs_psect;
	CodeBuffer.StartLC = 0;
	CodeBuffer.ExpectedLC = 0;
	RLDbuffer.count = 0;
}

/* =================================================================== */

void
CodeOut(byte opcode, byte place, boolean word_flag, psecttype psect,
	string symbol)
/* Puts code out to the listing and object files,	 */
/* also updates location counter.			 */

{
	if (pass > 1) {
		hex_(opcode, &ListBuffer.code[place - 1]);
		if (psect != abs_psect)
			ListBuffer.codeflag = '"';
		if (obj_option)
			binout(opcode, word_flag, psect, symbol);
	}
	LocCtr[current_psect] = (LocCtr[current_psect] + 1) % 65536L;
}

/* =================================================================== */
/* ====								=== */
/* ====			SYMBOL TABLE OPERATIONS			=== */
/* ====								=== */
/* =================================================================== */

void
addsym(int tblptr)
/* Makes room for a new symbol at SymTbl[tblptr], and inserts it.	 */
/* The symbol name is in token.TName.  As a side-effect,		 */
/* string_table.nextfree is updated.  The value is initialised to	 */
/* zero, the "defined", "equated", and "global" flags are set false,	 */
/* and the psect of the symbol is set to abs_psect.			 */


{
	int             j;
	Symbol_table_entry *temp;

	if (TraceFlag)
		In_Trace("addsym  ");
	if (nsyms == sytsiz)
		ErrMes('S');
	else {

		/* (a) make a space in the symbol table. */

		for (j = nsyms; j >= tblptr; j--)
			SymTbl[j] = SymTbl[j - 1];

		/* (b) insert the new symbol, being careful about flags. */

		nsyms++;
		temp = &SymTbl[tblptr - 1];
		temp->name = token.TName;
		temp->symval = 0;
		temp->defined_ = false;
		temp->equated = false;
		temp->sym_psect = abs_psect;

		string_table.nextfree += token.TName.length;
	}
	if (TraceFlag)
		OutTrace("addsym  ");
}

/* =================================================================== */

int
string_compare(string sa, string sb)
/* Compares the two strings in the string table.  Returns < 0	 */
/* if sa < sb, 0 if sa == sb, >0 if sa > sb.			 */

{
	int             N, result;

	if (sa.length <= sb.length)
		N = sa.length;
	else
		N = sb.length;

	result = strncmp(&string_table.val[sa.pointer - 1], &string_table.val[sb.pointer - 1], N);

	if (result == 0)
		if (sa.length < sb.length)
			result = -1;
		else if (sa.length > sb.length)
			result = 1;

	return result;
}

/* =================================================================== */

void
getsym(int *symptr, string sym_name,
       int *sym_value,
       boolean * sym_defined, boolean * sym_equated,
       psecttype * psect)
/* Gets symbol from user symbol table.  Symbol name is	 */
/* pointed to by sym_name; value is returned in sym_value,	 */
/* its place in the symbol table is returned in symptr.  The	 */
/* Boolean output parameters are set as follows:		 */
/* sym_defined:	symbol value is defined.		 */
/* sym_equated:	symbol may be updated.			 */
/* The symbol table SymTbl is kept sorted.			 */
/* Warning: if the symbol is not already in the symbol	 */
/* table, the symbol in token.TName is inserted.		 */
/* Therefore this void should not be called with a	 */
/* so-far-undefined symbol unless that symbol is the last	 */
/* symbol found by the scanner.				 */


{
	int             bottom, middle, top;
	Symbol_table_entry *temp;

	if (TraceFlag)
		In_Trace("getsym  ");
	if (testlevel > 10) {
		printf("Entering getsym.  Symbol is:\n");
		dump_string(sym_name);
	}
	bottom = 1;
	top = nsyms;
	while (bottom < top) {
		middle = (bottom + top) / 2;
		if (string_compare(SymTbl[middle - 1].name, sym_name) < 0)
			bottom = middle + 1;
		else
			top = middle;
	}

	/* End of search.  If symbol present,  bottom == top and	 */
	/* SymTbl[bottom] is the symbol sought.  Otherwise, the symbol	 */
	/* must be inserted at either SymTbl[bottom] or SymTbl[bottom+1]. */
	/* Note also the special case corresponding to nsyms == 0.	 */

	if ((bottom == top) && (string_compare(SymTbl[bottom - 1].name, sym_name) == 0)) {	/* symbol found */
		*symptr = bottom;
		temp = &SymTbl[*symptr - 1];
		*sym_value = temp->symval;
		*sym_defined = temp->defined_;
		*sym_equated = temp->equated;
		*psect = temp->sym_psect;
	} else {		/* symbol not found */
		if ((nsyms > 0) && (string_compare(sym_name, SymTbl[bottom - 1].name) > 0))
			bottom++;
		*symptr = bottom;
		*sym_value = 0;
		*sym_defined = false;
		*sym_equated = false;
		*psect = abs_psect;
		addsym(*symptr);
	}
	if (TraceFlag)
		OutTrace("getsym  ");
}

/* =================================================================== */

void
PutSym(string symbol_name, int symbol_value,
       boolean sym_equated, psecttype psect)
/* Puts a symbol into the symbol table.  Its "defined" flag	 */
/* is set equal to "true".					 */
/* N.B. the warning on void getsym applies here too.	 */

{
	int             j, symptr, old_value;
	byte            checksum, temp;
	boolean         already_defined, was_equated;
	psecttype       old_psect;

	if (TraceFlag)
		In_Trace("putsym  ");
	getsym(&symptr, symbol_name, &old_value, &already_defined, &was_equated,
	       &old_psect);

	/* If the symbol was previously listed as an external symbol, we	 */
	/* are now discovering that it's really an entry symbol.  Thus	 */
	/* we should treat it as a previously undefined symbol.  In	 */
	/* addition, we should put out a global symbol definition record. */
	/* This should only happen on pass 1 -- by pass 2, the only	 */
	/* external symbols left in the symbol table are those which are	 */
	/* genuinely external.						 */

	if ((pass == 1) && (old_psect == external_symbol)) {
		already_defined = false;
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
	}
	/* If value is undefined, update the flags.	 */

	if (!already_defined) {
		SymTbl[symptr - 1].defined_ = true;
		SymTbl[symptr - 1].equated = sym_equated;
		SymTbl[symptr - 1].sym_psect = psect;
	}
	/* Insert the symbol value. */

	if (already_defined && (was_equated != sym_equated))
		ErrMes('M');
	else if (already_defined && !sym_equated) {
		if (old_value != symbol_value)
			ErrMes('M');
	} else
		SymTbl[symptr - 1].symval = symbol_value;

	if (TraceFlag)
		OutTrace("putsym  ");
}

/* =================================================================== */

void
PrintSymbolTable()
/* Prints out the symbol table.  */

{
	int             j, k, count;

	if (TraceFlag)
		In_Trace("PrintSym");
	if (list_option) {
		count = 0;
		if (nsyms > 0)
			for (j = 0; j < nsyms; j++) {

				/*
				 * change the symbol table if (count > 72) {
				 * putc('\n', listing); count = 0; } while
				 * ((count & 7) != 0) { putc(' ', listing);
				 * count++; } if ((count +
				 * SymTbl[j].name.length) > 68) { putc('\n',
				 * listing); count = 0; } 
				 *
				 */

				if (SymTbl[j].equated)
					putc('=', listing);
				else
					putc(' ', listing);
				if (SymTbl[j].defined_)
					PrtHex(SymTbl[j].symval);
				else
					fprintf(listing, "****");
				if (SymTbl[j].sym_psect == external_symbol)
					putc('E', listing);
				else if (SymTbl[j].sym_psect == rel_psect)
					putc('\'', listing);
				else
					putc(' ', listing);
				putc(' ', listing);
				for (k = -1; k <= (SymTbl[j].name.length - 2); k++)
					putc(string_table.val[SymTbl[j].name.pointer + k], listing);

				/*
				 * original lines fprintf(listing, "    ");
				 * count += SymTbl[j].name.length + 11; 
				 */

				fprintf(listing, "\n");
			}
		fprintf(listing, "\n\n");
	}
	if (TraceFlag)
		OutTrace("PrintSym");
}

/* =================================================================== */
/* ====								=== */
/* ====			 EXPRESSIONS				=== */
/* ====								=== */
/* =================================================================== */
/*
 * void expr PP((int *result, psecttype *psect, string *external_symbol)); 
 */
/* =================================================================== */

void
primary(int *result, psecttype * psect, string * symbol)
/* Evaluates one primary element of an expression.  */


{
	int             flag, symptr;
	boolean         sym_defined, sym_equated;
	char            ch;

	if (token.TCode == 'A') {	/* identifier */
		flag = 0;
		if ((token.TName.length == 1)
		    && (string_table.val[token.TName.pointer - 1] == '.')) {
			*result = LocCtr[current_psect];
			*psect = current_psect;
			flag = 1;
		} else if (token.LookAhead == '(') {

			/* check for H(expr) or L(expr).	 */

			if (token.TName.length == 1) {
				ch = string_table.val[token.TName.pointer - 1];
				if (ch == 'H')
					flag = 1;
				else if (ch == 'L')
					flag = -1;
			}
			if (flag != 0) {
				scan();
				scan();
				expr(result, psect, symbol);
				if (*psect != abs_psect)
					ErrMes('X');
				*psect = abs_psect;
				if (token.TCode != ')')
					ErrMes(')');
				if (flag > 0)
					*result = shr8(*result);
				*result &= 256;
			}
		}
		if (flag == 0) {
			getsym(&symptr, token.TName, result,
			       &sym_defined, &sym_equated, psect);
			if (!sym_defined)
				ErrMes('U');
		}
		scan();
	} else if (token.TCode == '9') {
		*result = token.TValue;
		*psect = abs_psect;
		scan();
	} else {
		ErrMes('Q');
		*result = 0;
		*psect = abs_psect;
	}

}

/* =================================================================== */

void
factor(int *result, psecttype * psect,
       string * symbol)
/* Evaluates one factor in an expression.	 */

{
	if (token.TCode == '(') {
		scan();
		expr(result, psect, symbol);
		if (token.TCode == ')')
			scan();
		else
			ErrMes(')');
	} else
		primary(result, psect, symbol);
	return;
}

/* =================================================================== */

void
term(int *result, psecttype * psect,
     string * symbol)
/* Evaluates a term in the source line.	 */

{
	char            op;
	int             newfactor;
	psecttype       newpsect;
	string          newsymbol;


	/* Pick up first factor.	 */

	factor(result, psect, symbol);

	/* Now pick up all remaining factors. */

	do {
		op = ' ';
		if (token.TCode == '*')
			op = '*';
		else if (token.TCode == '/')
			op = '/';
		if (op != ' ') {
			scan();
			factor(&newfactor, &newpsect, &newsymbol);
			if ((*psect != abs_psect) || (newpsect != abs_psect)) {
				ErrMes('X');
				*result = 0;
			}
			*psect = abs_psect;
		}
		if (op == '*')
			*result *= newfactor;
		else if (op == '/')
			*result /= newfactor;

	} while (op != ' ');

}

/* =================================================================== */

void
expr(int *result, psecttype * psect, string * external_symbol_)
/* Evaluates an expression in the source line.	 */
/* The result is truncated to 16 bits.		 */
{
	char            op;
	int             newterm, swap;
	psecttype       newpsect;
	string          newsymbol;



	/* Pick up first term, or assume it is zero in	 */
	/* the case of unary plus or unary minus.	 */

	if ((token.TCode == '+') || (token.TCode == '-')) {
		*result = 0;
		*psect = abs_psect;
	} else
		term(result, psect, external_symbol_);

	/* Now pick up all remaining terms. */

	do {
		op = ' ';
		if ((token.TCode == '+') || (token.TCode == '-')) {
			op = token.TCode;
			scan();
			term(&newterm, &newpsect, &newsymbol);
		}
		if (op == '-') {
			if (newpsect == abs_psect) {
				newterm = -newterm;
				op = '+';
			} else if ((newpsect == rel_psect) && (*psect == rel_psect)) {
				*result -= newterm;
				*psect = abs_psect;
			} else
				ErrMes('X');
		}
		if (op == '+') {
			if (*psect == abs_psect) {
				swap = *result;
				*result = newterm;
				newterm = swap;
				*external_symbol_ = newsymbol;
				*psect = newpsect;
				newpsect = abs_psect;
			}
			if (newpsect != abs_psect)
				ErrMes('X');
			*result += newterm;
		}
	} while (op != ' ');

	if ((*result > 65536L) || (*result < -32768L))
		ErrMes('V');
	*result = *result % 65536L;
}

/* =================================================================== */

int
expr8()
{
	/* Like expr, but checks that the answer is absolute	 */
	/* and only 8 bits long.				 */

	int             answer;
	psecttype       psect;
	string          symbol;

	expr(&answer, &psect, &symbol);
	if (psect != abs_psect)
		ErrMes('V');
	if ((answer > 255) || (answer < -256))
		ErrMes('V');
	return (answer & 255);
}

/* =================================================================== */

int
RegName()
/* Looks for a register name, returns a register	 */
/* number, i.e. 0 for B, 1 for C, ... , 7 for A.	 */

{
	boolean         OKsofar, found;
	int             j, result;
	char            ch;


	/* Check that we have a one-letter identifier */

	OKsofar = (token.TCode == 'A') && (token.TName.length == 1);
	if (OKsofar) {		/* search the list of register names */
		ch = string_table.val[token.TName.pointer - 1];
		j = 0;
		found = false;
		while ((j < 8) && !found) {
			if (ch == register_list[j])
				found = true;
			else
				j++;
		}
		OKsofar = found;
	}
	if (OKsofar) {
		result = j;
		scan();
		return result;
	} else {
		ErrMes('R');
		return 0;
	}
}

/* =================================================================== */

int
DstName()
/* Same as regname, but multiplies the answer by eight. */

{
	return (RegName() * 8);
}

/* =================================================================== */

int
DRegName(int option)
/* Looks for a double register name, i.e. BC, DE, HL, AF, or SP.	 */
/* options are interpreted as follows:				 */
/* option == 5:	AF illegal					 */
/* option == 6:	SP illegal					 */
/* option == 7:	both AF and SP illegal				 */
/* Sets result = 0 for BC, 16 for DE, 32 for HL, 48 for AF or SP.	 */

{

	boolean         error, found;
	int             place, result;
	char            cha, chb;

	/* Check that we have a two-letter identifier */

	error = (token.TCode != 'A') || (token.TName.length != 2);

	if (!error) {		/* search the list of register names */
		place = 0;
		cha = string_table.val[token.TName.pointer - 1];
		chb = string_table.val[token.TName.pointer];
		do {
			found = (cha == register_list[place]);
			if (!found)
				place++;
		} while (!((place > 9) || (found)));

		/* check that second character matches. */

		found = found && (chb == register_list[place + 1]);
		error = !found;
	}
	if (!error) {
		if (place & 1) {

			/* If place is odd, we either have an error, or	 */
			/* the symbol was AF or SP.  Check these out.	 */
			/* (Will have 7 for AF, 9 for SP).		 */

			error = (((option != 5) || (place != 9))
				 && ((option != 6) || (place != 7)));

			place = 6;
		} else		/* Reject the 'names' MA, FS */
			error = (place > 4);
	}
	if (error)
		ErrMes('D');
	result = place * 8;
	scan();
	return result;
}

/* =================================================================== */

void
Operands(int opcode, int class)
/* Procedure to handle the operand fields (including the case of	 */
/* instructions which have no operands), and finish processing of	 */
/* the source line.							 */

{

	int             bufptr, x;
	psecttype       psect;
	string          symbol;

	if (TraceFlag)
		In_Trace("Operands");

	/* Put the location counter into the listing buffer. */

	PrtLC();
	bufptr = 1;

	/* Now the actual operand processing: */

	switch (class) {
	case 1:		/* no operands, nothing to do */
		break;
	case 2:		/* single destination register, e.g. dcr */
		opcode += DstName();
		break;
	case 3:		/* rst */
		x = expr8();
		if ((x < 0) || (x > 7))
			ErrMes('V');
		x = x & 7;
		opcode += 8 * x;
		break;
	case 4:		/* mov */
		opcode += DstName();
		if (token.TCode == ',')
			scan();
		else
			ErrMes(',');
		opcode += RegName();
		if (opcode == 118)
			ErrMes('H');
		break;
	case 5:
	case 6:
	case 7:		/* double register operand. class 5 is dad,
				 * dcx, inx. class 6 is pop, push. class 7 is
				 * ldax, stax.		 */
		opcode += DRegName(class);
		break;
	case 8:		/* mvi */
		opcode += DstName();
		CodeOut(opcode, bufptr, false, abs_psect, symbol);
		bufptr++;
		if (token.TCode == ',')
			scan();
		else
			ErrMes(',');
		opcode = expr8();
		break;
	case 9:
	case 10:		/* one immediate operand, e.g. adi or in */
		CodeOut(opcode, bufptr, false, abs_psect, symbol);
		bufptr++;
		opcode = expr8();
		break;
	case 11:		/* two-byte address field, e.g. jmp */
		CodeOut(opcode, bufptr, false, abs_psect, symbol);
		bufptr++;
		expr(&opcode, &psect, &symbol);
		CodeOut(opcode & 255, bufptr, true, psect,
			symbol);
		bufptr++;
		opcode = shr8(opcode);
		break;
	case 12:		/* lxi */
		opcode += DRegName(5);
		CodeOut(opcode, bufptr, false, abs_psect, symbol);
		bufptr++;
		if (token.TCode == ',')
			scan();
		else
			ErrMes(',');
		expr(&opcode, &psect, &symbol);
		CodeOut(opcode & 255, bufptr, true, psect,
			symbol);
		bufptr++;
		opcode = shr8(opcode);
		break;
	case 13:		/* single source register, e.g. add */
		opcode += RegName();
		break;
	default:
		printf("Error in Operands.\n");
	}

	/* Put out the last byte of the instruction. */

	CodeOut(opcode, bufptr, false, abs_psect, symbol);
	if (TraceFlag)
		OutTrace("Operands");
}

/* =================================================================== */

void
Labels()
/* Handles labels and also direct assignments. */

{
	boolean         nomore, def, equ, gbl;
	int             expr_val, symptr;
	string          LHSname, external_name;
	psecttype       psect;

	if (TraceFlag)
		In_Trace("Labels  ");

	do {

		nomore = true;

		/* If end of line reached, get a new one. */

		if (token.TCode == '\0') {
			if (pass > 1)
				ListTheLine();
			scan();
			nomore = false;
		} else if (token.TCode == 'A') {
			/*
			 * Recall that token.LookAhead holds a lookahead
			 * symbol 
			 */
			if (token.LookAhead == ':') {	/* label */
				PutSym(token.TName, LocCtr[current_psect], false,
				       current_psect);
				scan();
				scan();
				nomore = false;
			} else if (token.LookAhead == '=') {	/* assignment */
				LHSname = token.TName;

				/* The following call to getsym is only to	 */
				/* ensure that the symbol is put into the	 */
				/* symbol table in case it wasn't already	 */
				/* there.  Therefore, most of the parameters	 */
				/* are dummies.				 */

				getsym(&symptr, LHSname, &expr_val, &def, &equ, &psect);
				scan();
				scan();
				expr(&expr_val, &psect, &external_name);
				if ((LHSname.length == 1) &&
				    (string_table.val[LHSname.pointer - 1] == '.')) {
					if (psect != current_psect) {
						ErrMes('X');
						current_psect = psect;
					}
					LocCtr[current_psect] = expr_val;
				} else
					PutSym(LHSname, expr_val, true, psect);
				nomore = false;
				CkEol();
			}
		}
	} while (!((nomore) || (EndFlag)));	/* until nomore or EndFlag; */

	if (TraceFlag)
		OutTrace("Labels  ");
}

/* =================================================================== */

void
LookUp(int *opcode, int *class)
/* Looks up the opcode mnemonic table to determine the opcode and	 */
/* class of the mnemonic in token.TName.  If no match, a class	 */
/* of 0 is returned.							 */

{
	int             bottom, top, middle;
	boolean         found;
	sixchar         symbol;

	if (TraceFlag)
		In_Trace("Lookup  ");
	found = false;
	*class = 0;		/* Default if mnemonic not found */
	if ((token.TCode == 'A') && (token.TName.length <= 6)) {
		memcpy(symbol, "      ", sizeof(sixchar));
		for (middle = 0; middle < token.TName.length; middle++) {
			symbol[middle] = string_table.val[token.TName.pointer + middle - 1];
		}
		bottom = 1;
		top = Number_of_mnemonics;
		while (bottom < top) {
			middle = (bottom + top) / 2;
			if (strncmp(OpCodes[middle - 1].mnem, symbol, sizeof(sixchar)) < 0)
				bottom = middle + 1;
			else
				top = middle;
		}
		if ((bottom == top) && (!strncmp(OpCodes[bottom - 1].mnem, symbol, sizeof(sixchar))))
			found = true;
	}
	if (found) {
		*opcode = OpCodes[bottom - 1].i_code;
		*class = OpCodes[bottom - 1].i_class;

		/* Update token */

		if (*class == -3)
			skipblank();
		else
			scan();
	}
	if (TraceFlag)
		OutTrace("Lookup  ");
}

/* =================================================================== */

void
add_symbol(sixchar mnemonic, int opcode, int class)
/* Adds one entry to the permanent symbol table.	 */

{
	OpCodes_type   *temp;

	Number_of_mnemonics++;
	temp = &OpCodes[Number_of_mnemonics - 1];
	memcpy(temp->mnem, mnemonic, sizeof(sixchar));
	temp->i_code = opcode;
	temp->i_class = class;
}

/*----------------------------------------------------------*/


void
Init_Permanent_Symbol_Table()
{
	Number_of_mnemonics = 0;

	/********************************************/
	/****	WARNING: THE OPCODES HAVE NOT	****/
	/****	BEEN CAREFULLY CHECKED		****/
	/********************************************/

	add_symbol(".ABS  ", 0, -6);
	add_symbol(".ASCII", 0, -3);
	add_symbol(".BYTE ", 0, -1);
	add_symbol(".END  ", 0, -5);
	add_symbol(".GLOBL", 0, -8);
	add_symbol(".PAGE ", 0, -4);
	add_symbol(".REL  ", 0, -7);
	add_symbol(".WORD ", 0, -2);
	add_symbol("ACI   ", 206, 9);
	add_symbol("ADC   ", 136, 13);
	add_symbol("ADD   ", 128, 13);
	add_symbol("ADI   ", 198, 9);
	add_symbol("ANA   ", 160, 13);
	add_symbol("ANI   ", 230, 9);
	add_symbol("CALL  ", 205, 11);
	add_symbol("CC    ", 220, 11);
	add_symbol("CM    ", 252, 11);
	add_symbol("CMA   ", 47, 1);
	add_symbol("CMC   ", 63, 1);
	add_symbol("CMP   ", 184, 13);
	add_symbol("CNC   ", 212, 11);
	add_symbol("CNZ   ", 196, 11);
	add_symbol("CP    ", 244, 11);
	add_symbol("CPE   ", 236, 11);
	add_symbol("CPI   ", 254, 9);
	add_symbol("CPO   ", 228, 11);
	add_symbol("CZ    ", 204, 11);
	add_symbol("DAA   ", 39, 1);
	add_symbol("DAD   ", 9, 5);
	add_symbol("DCR   ", 5, 2);
	add_symbol("DCX   ", 11, 5);
	add_symbol("DI    ", 243, 1);
	add_symbol("EI    ", 251, 1);
	add_symbol("HLT   ", 118, 1);
	add_symbol("IN    ", 219, 10);
	add_symbol("INR   ", 4, 2);
	add_symbol("INX   ", 3, 5);
	add_symbol("JC    ", 218, 11);
	add_symbol("JM    ", 250, 11);
	add_symbol("JMP   ", 195, 11);
	add_symbol("JNC   ", 210, 11);
	add_symbol("JNZ   ", 194, 11);
	add_symbol("JP    ", 242, 11);
	add_symbol("JPE   ", 234, 11);
	add_symbol("JPO   ", 226, 11);
	add_symbol("JZ    ", 202, 11);
	add_symbol("LDA   ", 58, 11);
	add_symbol("LDAX  ", 10, 7);
	add_symbol("LHLD  ", 42, 11);
	add_symbol("LXI   ", 1, 12);
	add_symbol("MOV   ", 64, 4);
	add_symbol("MVI   ", 6, 8);
	add_symbol("NOP   ", 0, 1);
	add_symbol("ORA   ", 176, 13);
	add_symbol("ORI   ", 246, 9);
	add_symbol("OUT   ", 211, 10);
	add_symbol("PCHL  ", 233, 1);
	add_symbol("POP   ", 193, 6);
	add_symbol("PUSH  ", 197, 6);
	add_symbol("RAL   ", 23, 1);
	add_symbol("RAR   ", 31, 1);
	add_symbol("RC    ", 216, 1);
	add_symbol("RET   ", 201, 1);
	add_symbol("RIM   ", 32, 1);
	add_symbol("RLC   ", 7, 1);
	add_symbol("RM    ", 248, 1);
	add_symbol("RNC   ", 208, 1);
	add_symbol("RNZ   ", 192, 1);
	add_symbol("RP    ", 240, 1);
	add_symbol("RPE   ", 232, 1);
	add_symbol("RPO   ", 224, 1);
	add_symbol("RRC   ", 15, 1);
	add_symbol("RST   ", 199, 3);
	add_symbol("RZ    ", 200, 1);
	add_symbol("SBB   ", 152, 13);
	add_symbol("SBI   ", 222, 9);
	add_symbol("SHLD  ", 34, 11);
	add_symbol("SIM   ", 48, 1);
	add_symbol("SPHL  ", 249, 1);
	add_symbol("STA   ", 50, 11);
	add_symbol("STAX  ", 2, 7);
	add_symbol("STC   ", 55, 1);
	add_symbol("SUB   ", 144, 13);
	add_symbol("SUI   ", 214, 9);
	add_symbol("XCHG  ", 235, 1);
	add_symbol("XRA   ", 168, 13);
	add_symbol("XRI   ", 238, 9);
	add_symbol("XTHL  ", 227, 1);

}

/* =================================================================== */

void
Pseudo(int psenum)
/* Handles all assembler directives except '=='. */

{

	int             count, numval;
	char            delimiter, ch;
	psecttype       psect;
	string          symbol;

	if (TraceFlag)
		In_Trace("Pseudo  ");

	/* psenum == 0 means implicit .byte,	 */
	/* psenum == 1 means explicit .byte.	 */
	/* reduce these to a uniform case.	 */

	if (psenum == 0)
		psenum = 1;
	if (psenum < 4)
		PrtLC();

	/* Now handle each directive separately.  */

	count = 1;
	switch (psenum) {
	case 1:		/* .byte */
		do {
			if (count == 4) {
				newline();
				count = 1;
			}
			CodeOut(expr8(), count, false, abs_psect, symbol);
			if (token.TCode == ',') {
				scan();
				count++;
			} else
				count = 0;
		} while (count != 0);
		break;
	case 2:		/* .word */
		do {
			expr(&numval, &psect, &symbol);
			CodeOut(numval & 255, 1, true, psect, symbol);
			CodeOut(shr8(numval), 2, false, abs_psect, symbol);
			if (token.TCode == ',') {
				scan();
				newline();
			} else
				count = 0;
		} while (count != 0);
		break;
	case 3:		/* .ascii */
		delimiter = SrcBuf[SrcPtr - 1];
		SrcPtr++;
		do {
			ch = SrcBuf[SrcPtr - 1];
			if (ch == '\0') {
				ch = delimiter;
				ErrMes('A');
			} else
				SrcPtr++;
			if (ch != delimiter) {
				if (count == 4) {
					newline();
					count = 1;
				}
				CodeOut(ch, count, false, abs_psect, symbol);
				count++;
				ch = SrcBuf[SrcPtr - 1];
			} else {
				scan;
				count = 0;
			}
		} while (count != 0);
		break;
	case 4:		/* .page */
		LocCtr[current_psect] = 256 * ((LocCtr[current_psect] + 255) / 256);
		break;
	case 5:		/* .} */
		EndFlag = true;
		if (token.TCode != '\0') {
			StartAddress.Supplied = true;
			expr(&StartAddress.val, &StartAddress.psect, &symbol);
			if (StartAddress.psect == external_symbol)
				ErrMes('X');
		}
		break;
	case 6:		/* .abs	 */
		current_psect = abs_psect;
		break;
	case 7:		/* .rel	 */
		current_psect = rel_psect;
		break;
	case 8:		/* .globl	 */
		if (token.TCode == 'A') {
			if (pass == 1)
				PutSym(token.TName, 0, true, external_symbol);
			scan();
			break;
		} else
			ErrMes('G');
		while (token.TCode == ',') {
			scan();
			if (token.TCode == 'A') {
				if (pass == 1)
					PutSym(token.TName, 0, true, external_symbol);
				scan();
			} else
				ErrMes('G');
		}
		break;
	default:
		printf("Error in Pseudo : case statement. \n");
	}			/* of switch statement */
	if (TraceFlag)
		OutTrace("Pseudo  ");
}

/* =================================================================== */

void
OneLine()
/* Assembles a single line. */

{

	int             opcode, class;

	if (TraceFlag)
		In_Trace("OneLine ");
	scan();
	Labels();		/* Handle labels, symbol declarations */

	/* We have now handled all labels (if any).  token.TName should	 */
	/* be holding an instruction mnemonic or pseudo-op.		 */

	LookUp(&opcode, &class);
	if (class > 0)
		Operands(opcode, class);
	else if (!EndFlag)
		Pseudo(-class);
	CkEol();
	if (pass > 1)
		ListTheLine();
	if (TraceFlag)
		OutTrace("OneLine ");
}

/* =================================================================== */

void
OnePass()
/* One complete pass of the assembly.  */

{
	if (TraceFlag)
		In_Trace("OnePass ");
	EndFlag = false;
	LocCtr[abs_psect] = 0;
	LocCtr[rel_psect] = 0;
	current_psect = abs_psect;
	InitScanner();
	pass++;
	do
		OneLine();
	while (!EndFlag);
	if (TraceFlag)
		OutTrace("OnePass ");
}

/* =================================================================== */

void
Assemble()
/* Assembles a program. */

{

	byte            code, checksum;

	pass = 0;
	OnePass();		/* Pass 1 */

	/* End of pass 1.  Print the symbol table, and put an	 */
	/* "} GSD" record out to the object file.		 */


	PrintSymbolTable();
	if (obj_option) {
		checksum = 0;
		putobject(5, &checksum);
		putobject(2, &checksum);
		putobject((LocCtr[rel_psect] & 255), &checksum);
		putobject(shr8(LocCtr[rel_psect]), &checksum);
		fwrite(&checksum, sizeof(byte), 1, object);
	}
	/* Start pass 2.	 */

	rewind(sourcefile);
	ErrCount = 0;
	OnePass();		/* pass 2 */
	if (obj_option) {
		FlushBuffer();

		/* Write the "end module" record. */

		checksum = 0;
		code = 1;
		if (StartAddress.psect == rel_psect)
			code = 129;
		putobject(code, &checksum);
		if (StartAddress.Supplied) {
			putobject(2, &checksum);
			putobject(StartAddress.val & 255, &checksum);
			code = shr8(StartAddress.val);
		} else
			code = 0;
		putobject(code, &checksum);
		fwrite(&checksum, sizeof(byte), 1, object);
	}

	/* Add a newline to object file if not at eoln */
	if ( op_line_length < 16 ) 
		fprintf(opfile, "\n");

	if (list_option)
		putc('\n', listing);
	PrtHex(ErrCount);
	if (list_option)
		fprintf(listing, " Errors.");
}


/* =================================================================== */
/* ====								=== */
/* ====		 MAIN PROGRAM STARTS HERE.			=== */
/* ====								=== */
/* =================================================================== */

void main(int argc, char *argv[])
{


	TraceLevel = 0;
	list_option = true;
	obj_option = false; /* set this for binary output option */
	run_option = true;
	printf("\n Department of Electrical and Computer Engineering\n");
	printf("                University of Newcastle\n");
	printf("       ******* 8085/8080 Cross Assembler *******\n\n");

	if (argc < 3) {
		printf("\n USAGE : as85 input_filename output_filename listing_filename.\n\n");
		exit(1);
	}
	if ((sourcefile = fopen(argv[1], "r")) == NULL) {
		printf("Error : Unable to open %s for input.\n", argv[1]);
		exit(1);
	}
	if ((opfile = fopen(argv[2], "w")) == NULL) {
		printf("Error : Unable to open %s for opcode.\n", argv[2]);
		exit(1);
	}

	/* Used for binary output option
	*	if ((object = fopen(argv[2], "wb")) == NULL) {
	*		printf("Error : Unable to open %s for object.\n", argv[2]);
	*		exit(1);
	*	}
	*/

	if ((listing = fopen(argv[3], "w")) == NULL) {
		printf("Error : Unable to open %s for listing.\n", argv[3]);
		exit(1);
	}
	rewind(sourcefile);

	Init_Permanent_Symbol_Table();

	register_list[0] = 'B';
	register_list[1] = 'C';
	register_list[2] = 'D';
	register_list[3] = 'E';
	register_list[4] = 'H';
	register_list[5] = 'L';
	register_list[6] = 'M';
	register_list[7] = 'A';
	register_list[8] = 'F';
	register_list[9] = 'S';
	register_list[10] = 'P';

	string_table.nextfree = 1;
	InitBinout();
	StartAddress.Supplied = false;
	StartAddress.psect = abs_psect;
	nsyms = 0;		/* # of symbol table entries */

	Assemble();
	if (ErrCount == 0)
		printf(" No errors.\n\n");
	else
		printf(" %3i errors.\n\n", ErrCount);



	if (fclose(sourcefile) != 0)
		printf("Error : problem closing input file.\n");
	if (fclose(opfile) != 0)
		printf("Error : problem closing opcode file.\n");

	 /*
	 *	if (fclose(object) != 0)
	 *		printf("Error : problem closing object file.\n");
	 */

	if (fclose(listing) != 0)
		printf("Error : problem closing listing file.\n");

}
