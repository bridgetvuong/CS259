/**CHeaderFile*****************************************************************

  FileName    [mu_real.hpp]

  Synopsis    [Header file for finite precision real numbers]

  Author      [Igor Melatti]

  Copyright   [
  This file is part of the verifier package of CMurphi. 
  Copyright (C) 2009-2012 by Sapienza University of Rome. 

  CMurphi is free software; you can redistribute it and/or 
  modify it under the terms of the GNU Lesser General Public 
  License as published by the Free Software Foundation; either 
  of the License, or (at your option) any later version.

  CMurphi is distributed in the hope that it will be useful, 
  but WITHOUT ANY WARRANTY; without even the implied warranty of 
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU 
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public 
  License along with this library; if not, write to the Free Software 
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.

  To contact the CMurphi development board, email to <melatti@di.uniroma1.it>. ]

******************************************************************************/

#ifndef _REALCLASS_
#define _REALCLASS_

/* AP: class mu__real's declaration (base for real numbers) */
class mu__real {
  static double undef_value;	//AP: undef_value for real type

  void operator=(mu__real &);

protected:
  int accuracy, exponent;	// AP: accuracy is the number of decimal digit used to represent a real
  // AP: exponent is the number of digit used for the exponent
  int exponent_value;		// IM: maximum positive exponent value (negative is -exponent_value+1)
  bool in_world;		// if TRUE global variable, otherwise local
  int offset, size;		// offset in the state vector, size (both in bits)
  int size_in_byte;		// AP: size in byte
  char format_string_1[10];	// AP: format_string_1 contains the format string used for write a
  // AP: real number to the state vector
  // AP: Ex: if accuracy = 6 then format_string_1 = "%+.5Le".        //IM: "%+.5le"
  char format_string_2[300];	// AP: format_string_2 contains the format string used for print
  // AP: the value of a real variable (see function Print())
  // AP: Ex: if name = "x" and accuracy = 6 then
  // AP: format_string_2 = "x:%+.5Le"                                                        //IM: "x:%+.5le"
  // AP: Note: the size of format_string_2 also depends on
  // AP: the length of an identifier
#ifdef ALIGN
  int byteOffset;		// offset in state vector in bytes
#endif
  bool initialized;		// whether it is initialized in the startstate
  //    Uli: seems not to be used any more
  double cvalue;		// contains value of local variable

public:
  char *name;			// name of the variable
  char longname[BUFFER_SIZE / 4];

  // constructors
   mu__real(int accuracy, int exponent, int size, const char *n, int os):accuracy(accuracy), exponent_value(exponent), size(size), initialized(FALSE)	//IM: exponent given to this->exponent_value and not to exponent
  {
    setexponentdigits();	//IM: sets this->exponent
    set_formats_string();
    set_self(n, os);
    size_in_byte = div(size, 8).quot;
    undefined();
  };

  mu__real(int accuracy, int exponent, int size):accuracy(accuracy), exponent_value(exponent), size(size), initialized(FALSE)	//IM: exponent given to this->exponent_value and not to exponent
  {
    setexponentdigits();	//IM: sets this->exponent
    set_formats_string();
    set_self(NULL, 0);
    size_in_byte = div(size, 8).quot;
    undefined();
  };

  // Uli: - seems not to be used any more
  //      - however, I left it here since it does the correct things
  mu__real(int accuracy, int precision, int size,
	   double val):accuracy(accuracy), exponent_value(exponent),
      size(size)
      //IM: exponent given to this->exponent_value and not to exponent
  {
    setexponentdigits();	//IM: sets this->exponent
    set_self("Parameter or function result", 0);
    set_formats_string();	//IM: was after the assignment below, probably was an error
    operator=(val);
    size_in_byte = div(size, 8).quot;
  };

  // Uli: this constructor is called implicitly for function results
  //      by the code generated by the Murphi compiler
  mu__real(const mu__real & src)
  :accuracy(src.accuracy), exponent_value(src.exponent_value),
      size(src.size), in_world(FALSE)
      //IM: exponent given to this->exponent_value and not to exponent
  {
    setexponentdigits();	//IM: sets this->exponent
    set_formats_string();	//IM:fixed, was after the call to value
    set_self("Function result", 0);
    value(src.value());		// value() returning undefined values
    size_in_byte = div(size, 8).quot;
  };

  // a destructor
  ~mu__real() {
  };

  void setexponentdigits()	//IM: number of digits of exponent_value
  {
    char buf[10];

    sprintf(buf, "%+d", exponent_value);
    exponent = strlen(buf) - 1;
  }


  // routine for constructor use
  void set_self_ar(const char *n1, const char *n2, int os) {
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy(longname, n1);
    longname[l1] = '[';
    strcpy(longname + l1 + 1, n2);
    longname[l1 + l2 + 1] = ']';
    longname[l1 + l2 + 2] = 0;
    set_self(longname, os);
  };

  void set_self_2(const char *n1, const char *n2, int os) {
    strcpy(longname, n1);
    strcat(longname, n2);
    set_self(longname, os);
  };

  void set_self(const char *n, int os) {
    if (n != NULL) {
      name = new char[strlen(n) + 1];
      strcpy(name, n);
    } else
      name = NULL;
    offset = os;
    in_world = FALSE;		// Uli: variables are local by default

#ifdef ALIGN
    byteOffset = offset / 8;
#endif
  };

// assignment
  double operator=(double val) {
    return value(val);
  }

#ifndef NO_RUN_TIME_CHECKING
  void undef_error() const;
  inline operator   double () const {
    if (isundefined())
      undef_error();
    return value();
  };
#else
  inline operator   double () const {
    return value();
  };
#endif

  // AP: data access routines

  inline void clear() {
    value((double) 0);
    initialized = TRUE;
  };
  inline void undefine() {
    undefined();
    initialized = TRUE;
  };
  inline void reset() {
    undefined();
    initialized = FALSE;
  };

  // AP: routine for setting undef_value
  inline static double set_undef_value() {
    char buf[20];
    double x, y;

    x = 0;
    sprintf(buf, "%+le", x);
    buf[0] = '-';
    sscanf(buf, "%le", &y);

    return y;
  };

  // AP: routine for setting format_string_1 and format_string_2
  void set_formats_string() {
    char buf[10];

    cout.setf(ios::scientific);
    cout.precision(8);

    strcpy(format_string_1, "%+.");
    strcpy(format_string_2, "%s:");
    sprintf(buf, "%dle", accuracy - 1);
    strcat(format_string_1, buf);
    strcat(format_string_2, format_string_1);
  };

  // AP: routine used to compact buf in order to store a double value in size_in_byte byte
  // AP: of the state vector
  unsigned char *compact_buf(char *buf) {
    char aux_buf[100] = "\0";
    unsigned char *zip_buf;
    int diff_length;
    unsigned short i, offset;
    unsigned char c1, c2;

    //AP: initialed zip_buf
    zip_buf =
	(unsigned char *) malloc((size_in_byte + 1) *
				 sizeof(unsigned char));
    if (zip_buf == NULL)
      Error.Error("Error in compact_buf: unable to allocate memory.");

    // AP: aux_buf contains buf without '.' and 'e'
    strncpy(aux_buf, buf, 2);
    strncat(aux_buf, buf + 3, accuracy - 1);
    offset = accuracy > 1 ? 3 : 2;	// AP: offset is used to handle the special case accuracy = 1
    strcat(aux_buf, buf + accuracy + offset);
    if ((diff_length = strlen(aux_buf) - 2 * size_in_byte) > 0)	// AP: aux_buf needs more than 'size_in_byte' byte;
      // AP: this case can occur when value's exponent
      // AP: take up more than 'exponent' byte;
      // AP: the only thing to do is to verify that
      // AP: whith a loss of accuracy value fits in state vector
    {
      if ((diff_length - accuracy) >= 0)	// AP: can't have a number with accuracy less or equal to zero
	Error.Error(tsprintf
		    ("Error in compact_buf: unable to store %s in state vector",
		     buf));

      strcpy(buf, "");		// AP: reset buf
      strncat(buf, aux_buf, accuracy - diff_length + 1);	// AP: copy aux_buf in buf with loss of accuracy
      strcat(buf, aux_buf + accuracy + 1);

      strcpy(aux_buf, "");	// AP: reset aux_buf
      strcpy(aux_buf, buf);	// AP: copy buf in aux_buf
    }

    /* AP: compacting aux_buf. This is the code:
       0 -> 0001       7 -> 1000
       1 -> 0010       8 -> 1001
       2 -> 0011       9 -> 1010
       3 -> 0100       + -> 1011
       4 -> 0101       - -> 1100
       5 -> 0110         -> 1101    this is used when the aux_buf's length is odd
       6 -> 0111
       Note: the code start with 0001 because '\0' is the null character of a string */

    if ((strlen(aux_buf) % 2) != 0)	// AP: aux_buf's length is odd
      aux_buf[strlen(aux_buf)] = 13;	// AP: the auxiliary code is put in the last position of aux_buf
    // AP: now, aux_buf's length is even

    aux_buf[strlen(aux_buf)] = '\0';

    for (i = 0; i < strlen(aux_buf); i += 2) {
      switch (aux_buf[i])	// AP: setting c1
      {
      case '+':{
	  c1 = 11;
	  break;
	}
      case '-':{
	  c1 = 12;
	  break;
	}
      default:{
	  c1 = aux_buf[i] - '0' + 1;
	}
      }
      switch (aux_buf[i + 1])	// AP: setting c2
      {
      case '+':{
	  c2 = 11;
	  break;
	}
      case '-':{
	  c2 = 12;
	  break;
	}
      case 13:{
	  c2 = 13;
	  break;
	}
      default:{
	  c2 = aux_buf[i + 1] - '0' + 1;
	}
      }

      c1 = (c1 << 4) | c2;	// AP: now, c1 and c2 will take up a byte in zipbuf
      zip_buf[i / 2] = c1;
    }
    zip_buf[i / 2] = '\0';
    return zip_buf;
  };

  // AP: routine used to decompact buf in order to read a double value from the state vector
  char *decompact_buf(unsigned char *buf) const {
    unsigned char c;
    char c1, c2;
    unsigned short i, j;
    char *unzip_buf;
    char aux_buf[100];

    //AP: initialed unzip_buf
     unzip_buf =
	(char *) malloc((accuracy + exponent + 20) * sizeof(char));
    if (unzip_buf == NULL)
      Error.Error("Error in decompact_buf: unable to allocate memory.");

     j = 0;
    for (i = 0; i < size_in_byte; i++) {
      // AP: decompacting in aux_buf
      c = buf[i];
      c1 = c >> 4;
      c2 = c & 0xF;

      switch (c1)		// AP: setting c1
      {
      case 11:{
	  c1 = '+';
	  break;
	} case 12: {
	  c1 = '-';
	  break;
	}
      default:{
	  c1 = c1 + '0' - 1;
	}
      }
      switch (c2)		// AP: setting c2
      {
      case 11:{
	  c2 = '+';
	  break;
	}
      case 12:{
	  c2 = '-';
	  break;
	}
      case 13:{
	  c2 = 13;
	  break;
	}
      default:{
	  c2 = c2 + '0' - 1;
	}
      }
      aux_buf[j++] = c1;
      aux_buf[j++] = c2;
    }
    aux_buf[j] = '\0';
    // AP: now, we can build unzip_buf storing a double value
    j = 0;
    for (i = 0; i < strlen(aux_buf); i++) {
      if (i == 2)
	unzip_buf[j++] = '.';
      if (((aux_buf[i] == '+') || (aux_buf[i] == '-')) && (i > 0))
	unzip_buf[j++] = 'e';
      if (aux_buf[i] != 13)
	unzip_buf[j++] = aux_buf[i];
    }
    unzip_buf[j] = '\0';
    return unzip_buf;
  };

#ifdef ALIGN
  // AP: routine used to store a double value in the state vector when the states aren't bit-compacted
  void setreal(double value) {
    char buf[100];
    unsigned char *zip_buf;
    unsigned short i;

    sprintf(buf, format_string_1, value);	// AP: buf contains value

    zip_buf = compact_buf(buf);	// AP: now, we can copy zip_buf in bits
    for (i = 0; i < size_in_byte; i++) {
      workingstate->bits[i + byteOffset] = zip_buf[i];
    }
    free(zip_buf);
  };
#else
  // AP: routine used to modify the struct where of position type on the basis of offset's value
  inline void set_where(int offset, position & where) const {
    where.longoffset = offset / 32;
    where.shift1 = offset % 32;
    where.mask1 = (1 << 8) - 1;
    where.mask1 <<= where.shift1;
    where.mask2 = 0;
    if ((offset + 8) / 32 != where.longoffset) {
      where.shift2 = 32 - where.shift1;
      where.mask2 = (1 << (8 - where.shift2)) - 1;
    }
    where.longoffset *= 4;
  };

  // AP: routine used to store a double value in the state vector when the states are bit-compacted (option -b)
  void setrealb(double value) {
    char buf[100];
    unsigned char *zip_buf;
    unsigned short i;
    int os;
    position where;

    sprintf(buf, format_string_1, value);	// AP: buf contains value

    zip_buf = compact_buf(buf);	// AP: now, we can copy zip_buf in bits

    // AP: in order to store zip_buf in bits when the states are bit-compacted we simply call
    // AP: set() size_in_byte times
    os = offset;
    for (i = 0; i < size_in_byte; i++) {
      set_where(os, where);
      workingstate->set(&where, zip_buf[i]);
      os += 8;
    }
    free(zip_buf);
  };
#endif

#ifdef ALIGN
  // AP: routine used to read a double value from the state vector when the states aren't bit-compacted
  double getreal(state * st) const {
    unsigned char buf[100];
    char *unzip_buf;
    double x;
    unsigned short i;

    for (i = 0; i < size_in_byte; i++) {
      buf[i] = st->bits[i + byteOffset];
    } buf[i] = '\0';
    unzip_buf = decompact_buf(buf);
    sscanf(unzip_buf, "%le", &x);
    free(unzip_buf);
    return x;
  };
#else
  // AP: routine used to read a double value from the state vector when the states are bit-compacted (option -b)
  double getrealb(state * st) const {
    unsigned char buf[100];
    char *unzip_buf;
    double x;
    unsigned short i;
    int os;
    position where;

    // AP: in order to read a double from bits when the states are bit-compacted we simply call
    // AP: get() size_in_byte times
     os = offset;
    for (i = 0; i < size_in_byte; i++) {
      set_where(os, where);
      buf[i] = st->get(&where);
      os += 8;
    } buf[i] = '\0';
    unzip_buf = decompact_buf(buf);
    sscanf(unzip_buf, "%le", &x);
    free(unzip_buf);
    return x;
  };
#endif

  inline double value() const {
    if (in_world)
#ifdef ALIGN
      return getreal(workingstate);
#else
      return getrealb(workingstate);
#endif
    else
      return cvalue;
  };

  inline double value(double val) {	//im: fixed to manage exponent limits
    char *buf, *tmp;
    int ex_value;

    buf = tsprintf(format_string_1, val);
    if (!(strcmp(buf, "+nan")) || !(strcmp(buf, "-nan")))
      Error.
	  Error("Error in value(val): probably either division by zero.");
    if (!(strcmp(buf, "+inf")) || !(strcmp(buf, "-inf")))
      Error.Error("Error in value(val): exponent out of bounds.");
    tmp = strstr(buf, "e");
    sscanf(++tmp, "%d", &ex_value);	//im: jump 'e'
    if (ex_value < -exponent_value + 1)
      val = (double) 0;
    else if (ex_value > exponent_value)
      Error.Error("Error in value(val): exponent %d out of bounds.",
		  ex_value);

    if (in_world)
#ifdef ALIGN
      setreal(val);
#else
      setrealb(val);
#endif
    else {
      sscanf(buf, "%le", &val);	//gdp: adjust precision of value      //im: used only in this case, setreal(b) doesn't need this
      cvalue = val;
    }
    free(buf);
    return val;
  };


  inline void undefined() {
    defined(FALSE);
  };

  inline void defined(bool val) {
    if (!val)
      if (!in_world)
	cvalue = undef_value;
      else
#ifdef ALIGN
	setreal(undef_value);
#else
	setrealb(undef_value);
#endif
  };

  inline bool defined() const {
    double x;
    char *buf1, *buf2;

    bool isdefined;
    if (in_world)
#ifdef ALIGN
       x = getreal(workingstate);
#else
       x = getrealb(workingstate);
#endif
    else
       x = cvalue;
     buf1 = tsprintf("%+le", undef_value);
     buf2 = tsprintf("%+le", x);
     isdefined = strcmp(buf1, buf2);
     free(buf1);
     free(buf2);
     return (isdefined);
  };


  inline bool isundefined() const {
    return !(defined());
  };


// printing, etc.
  virtual void print() {
    char c;

    if (defined()) {
      printf(format_string_2, name, value());
      printf("\n");
    } else
      cout << name << ":Undefined\n";
  };

  friend ostream & operator<<(ostream & s, mu__real & val) {
    if (val.defined())
      s << (double) val.value();
    else
      s << "Undefined";
    return s;
  }

  void print_diff(state * prev);

  // transfer routines
  void to_state(state * thestate) {
    double val = value();	// Uli: copy value (which is probably undefined)
    in_world = TRUE;
    value(val);
  };

  void from_state(state * thestate) {
  };

  // comparing routines, for symmetry
  friend int CompareWeight(mu__real & a, mu__real & b) {
    if (!a.defined() && !b.defined())
      return 0;
    else if (!a.defined())
      return -1;
    else if (!b.defined())
      return 1;
    else if (a.value() == b.value())
      return 0;
    else if (a.value() > b.value())
      return 1;
    else
      return -1;
  };

  friend int Compare(mu__real & a, mu__real & b) {
    if (!a.defined() && !b.defined())
      return 0;
    else if (!a.defined())
      return -1;
    else if (!b.defined())
      return 1;
    else if (a.value() == b.value())
      return 0;
    else if (a.value() > b.value())
      return 1;
    else
      return -1;
  };
  virtual void MultisetSort() {
  };
};

#endif
