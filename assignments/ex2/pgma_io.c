# include <stdlib.h>
# include <string.h>
# include <math.h>

# include "pgma_io.h"

/******************************************************************************/

int i4_min ( int i1, int i2 )

/******************************************************************************/
/*
  Purpose:

    I4_MIN returns the minimum of two I4's.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    13 October 1998

  Author:

    John Burkardt

  Parameters:

    Input, int I1, I2, two integers to be compared.

    Output, int I4_MIN, the smaller of I1 and I2.
*/
{
  int value;

  if ( i1 < i2 )
  {
    value = i1;
  }
  else
  {
    value = i2;
  }
  return value;
}
/******************************************************************************/

void pgma_check_data ( int xsize, int ysize, int maxg, int *g )

/******************************************************************************/
/*
  Purpose:

    PGMA_CHECK_DATA checks the data for an ASCII PGM file.

  Discussion:

    XSIZE and YSIZE must be positive, the pointers must not be null,
    and the data must be nonnegative and no greater than MAXG.

  Example:

    P2
    # feep.pgm
    24 7
    15
    0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0
    0  3  3  3  3  0  0  7  7  7  7  0  0 11 11 11 11  0  0 15 15 15 15  0
    0  3  0  0  0  0  0  7  0  0  0  0  0 11  0  0  0  0  0 15  0  0 15  0
    0  3  3  3  0  0  0  7  7  7  0  0  0 11 11 11  0  0  0 15 15 15 15  0
    0  3  0  0  0  0  0  7  0  0  0  0  0 11  0  0  0  0  0 15  0  0  0  0
    0  3  0  0  0  0  0  7  7  7  7  0  0 11 11 11 11  0  0 15  0  0  0  0
    0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    05 June 2010

  Author:

    John Burkardt

  Parameters:

    Input, int XSIZE, YSIZE, the number of rows and columns of data.

    Input, int MAXG, the maximum gray value.

    Input, int *G, the array of XSIZE by YSIZE data values.
*/
{
  int i;
  int *index;
  int j;
  int k;

  if ( xsize <= 0 )
  {
    fprintf ( stderr, "\n" );
    fprintf ( stderr, "PGMA_CHECK_DATA: Error!\n" );
    fprintf ( stderr, "  XSIZE <= 0.\n" );
    fprintf ( stderr, "  XSIZE = %d\n", xsize );
    exit ( 1 );
  }

  if ( ysize <= 0 )
  {
    fprintf ( stderr, "\n" );
    fprintf ( stderr, "PGMA_CHECK_DATA: Error!\n" );
    fprintf ( stderr, "  YSIZE <= 0.\n" );
    fprintf ( stderr, "  YSIZE = %d\n", ysize );
    exit ( 1 );
  }

  if ( g == NULL )
  {
    fprintf ( stderr, "\n" );
    fprintf ( stderr, "PGMA_CHECK_DATA: Error!\n" );
    fprintf ( stderr, "  Null pointer to g.\n" );
    exit ( 1 );
  }

  index = g;

  for ( j = 0; j < ysize; j++ )
  {
    for ( i = 0; i < xsize; i++ )
    {
      if ( *index < 0 )
      {
        fprintf ( stderr, "\n" );
        fprintf ( stderr, "PGMA_CHECK_DATA - Fatal error!\n" );
        fprintf ( stderr, "  Negative data.\n" );
        fprintf ( stderr, "  G(%d,%d)=%d\n", i, j, *index );
        exit ( 1 );
      }
      else if ( maxg < *index )
      {
        fprintf ( stderr, "\n" );
        fprintf ( stderr, "PGMA_CHECK_DATA - Fatal error!\n" );
        fprintf ( stderr, "  Data exceeds MAXG = %d\n", maxg );
        fprintf ( stderr, "  G(%d,%d)=%d\n", i, j, *index );
        exit ( 1 );
      }

      index = index + 1;
    }
  } 

  return;
}
/******************************************************************************/

void pgma_example ( int xsize, int ysize, int *g )

/******************************************************************************/
/*
  Purpose:

    PGMA_EXAMPLE sets up some data for an ASCII PGM file.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    05 June 2010

  Author:

    John Burkardt

  Parameters:

    Input, int XSIZE, YSIZE, the number of rows and columns of data.

    Output, int *G, the array of XSIZE by YSIZE gray values.
*/
{
  int i;
  int *indexg;
  int j;
  int periods = 3;
  double PI = 3.14159265;
  double x;
  double y;

  indexg = g;

  for ( i = 0; i < ysize; i++ )
  {
    y = ( ( double ) ( 2 * i ) ) / ( ( double ) ( ysize - 1 ) ) - 1.0;

    for ( j = 0; j < xsize; j++ )
    {
      x = ( 2.0 * PI * ( double ) ( periods * j ) ) / ( ( double ) ( xsize - 1 ) );

      *indexg = ( int ) ( 20.0 * ( sin ( x ) - y + 2 ) );
 
      indexg = indexg + 1;
    }
  }

  return;
}
/******************************************************************************/

void pgma_read ( char *file_in_name, int *xsize, int *ysize, int *maxg,
  int **g )

/******************************************************************************/
/*
  Purpose:

    PGMA_READ reads the header and data from an ASCII PGM file.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:
 
    05 June 2010
 
  Author:
 
    John Burkardt

  Parameters:

    Input, char *FILE_IN_NAME, the name of the file.

    Output, int *XSIZE, *YSIZE, the number of rows and columns of data.

    Output, int *MAXG, the maximum gray value.

    Output, int **G, the array of XSIZE by YSIZE data values.
*/
{
  int error;
  FILE *file_in;
  int numbytes;

  file_in = fopen ( file_in_name, "rt" );

  if ( !file_in )
  {
    fprintf ( stderr, "\n" );
    fprintf ( stderr, "PGMA_READ - Fatal error!\n" );
    fprintf ( stderr, "  Cannot open the input file \"%s\".\n",
      file_in_name );
    exit ( 1 );
  }
/*
  Read the header.
*/
  pgma_read_header ( file_in, xsize, ysize, maxg );
/*
  Allocate storage for the data.
*/
  numbytes = ( *xsize ) * ( *ysize ) * sizeof ( int );

  *g = ( int * ) malloc ( numbytes * sizeof ( int ) );
/*
  Read the data.
*/
  pgma_read_data ( file_in, *xsize, *ysize, *g );
/*
  Close the file.
*/
  fclose ( file_in );

  return;
}
/******************************************************************************/

void pgma_read_data ( FILE *file_in, int xsize, int ysize, int *g )

/******************************************************************************/
/*
  Purpose:

    PGMA_READ_DATA reads the data in an ASCII PGM file.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    04 June 2010

  Author:

    John Burkardt

  Parameters:

    Input, FILE *FILE_IN, a pointer to the file containing the data.

    Input, int XSIZE, YSIZE, the number of rows and columns of data.

    Output, int *G, the array of XSIZE by YSIZE data values.
*/
{
  int i;
  int j;
  int n;

  for ( j = 0; j < ysize; j++ )
  {
    for ( i = 0; i < xsize; i++ )
    {
      n = fscanf ( file_in, "%d", g );

      if ( n != 1 )
      {
        fprintf ( stderr, "\n" );
        fprintf ( stderr, "PGMA_READ_DATA - Fatal error!\n" );
        fprintf ( stderr, "  Unable to read data.\n" );
        exit ( 1 );
      }
      g = g + 1;
    }
  }
  return;
}
/******************************************************************************/

void pgma_read_header ( FILE *file_in, int *xsize, int *ysize, int *maxg )

/******************************************************************************/
/*
  Purpose:

    PGMA_READ_HEADER reads the header of an ASCII PGM file.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    05 June 2010

  Author:

    John Burkardt

  Parameters:

    Input, FILE *FILE_IN, a pointer to the file.

    Output, int *XSIZE, *YSIZE, the number of rows and columns of data.

    Output, int *MAXG, the maximum gray value.
*/
{
# define LINE_MAX 255

  int count;
  char *error;
  char line[LINE_MAX];
  char *next;
  int step;
  int width;
  char word[LINE_MAX];

  step = 0;

  while ( 1 )
  {
    error = fgets ( line, LINE_MAX, file_in );

    if ( !error )
    {
      fprintf ( stderr, "\n" );
      fprintf ( stderr, "PGMA_READ_HEADER - Fatal error!\n" );
      fprintf ( stderr, "  End of file.\n" );
      exit ( 1 );
    }

    next = line;

    if ( line[0] == '#' )
    {
      continue;
    }

    if ( step == 0 )
    {
      count = sscanf ( next, "%s%n", word, &width );
      if ( count == EOF )
      {
        continue;
      }
      next = next + width;
      if ( strcmp ( word, "P2" ) != 0 && strcmp ( word, "p2" ) != 0 )
      {
        fprintf ( stderr, "\n" );
        fprintf ( stderr, "PGMA_READ_HEADER - Fatal error.\n" );
        fprintf ( stderr, "  Bad magic number = \"%s\".\n", word );
        exit ( 1 );
      }
      step = 1;
    }

    if ( step == 1 )
    {

      count = sscanf ( next, "%d%n", xsize, &width );
      next = next + width;
      if ( count == EOF )
      {
        continue;
      }
      step = 2;
    }

    if ( step == 2 )
    {
      count = sscanf ( next, "%d%n", ysize, &width );
      next = next + width;
      if ( count == EOF )
      {
        continue;
      }
      step = 3;
    }

    if ( step == 3 )
    {
      count = sscanf ( next, "%d%n", maxg, &width );
      next = next + width;
      if ( count == EOF )
      {
        continue;
      }
      break;
    }

  }

  return;
# undef LINE_MAX
}
/******************************************************************************/

void pgma_read_test ( char *file_in_name )

/******************************************************************************/
/*
  Purpose:

    PGMA_READ_TEST tests the ASCII PGM read routines.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    05 June 2010

  Author:

    John Burkardt

  Parameters:

    Input, char *FILE_IN_NAME, the name of the file.
*/
{
  int *g;
  int maxg;
  int xsize;
  int ysize;

  g = NULL;
/*
  Read the data.
*/
  pgma_read ( file_in_name, &xsize, &ysize, &maxg, &g );

  fprintf ( stdout, "\n" );
  fprintf ( stdout, "PGMA_READ_TEST:\n" );
  fprintf ( stdout, "  PGMA_READ was able to read \"%s\".\n", file_in_name );
/*
  Check the data.
*/
  pgma_check_data ( xsize, ysize, maxg, g );

  free ( g );

  fprintf ( stdout, "\n" );
  fprintf ( stdout, "PGMA_READ_TEST:\n" );
  fprintf ( stdout, "  PGMA_CHECK_DATA has approved the data from the file.\n" );

  return;
}
/******************************************************************************/

void pgma_write ( char *file_out_name, int xsize, int ysize, int *g )

/******************************************************************************/
/*
  Purpose:

    PGMA_WRITE writes the header and data for an ASCII PGM file.
 
  Example:

    P2
    # feep.pgm
    24 7
    15
    0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0
    0  3  3  3  3  0  0  7  7  7  7  0  0 11 11 11 11  0  0 15 15 15 15  0
    0  3  0  0  0  0  0  7  0  0  0  0  0 11  0  0  0  0  0 15  0  0 15  0
    0  3  3  3  0  0  0  7  7  7  0  0  0 11 11 11  0  0  0 15 15 15 15  0
    0  3  0  0  0  0  0  7  0  0  0  0  0 11  0  0  0  0  0 15  0  0  0  0
    0  3  0  0  0  0  0  7  7  7  7  0  0 11 11 11 11  0  0 15  0  0  0  0
    0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:
 
    05 June 2010
 
  Author:
 
    John Burkardt

  Parameters:

    Input, char *FILE_OUT_NAME, the name of the file.

    Input, int XSIZE, YSIZE, the number of rows and columns of data.

    Input, int *G, the array of XSIZE by YSIZE data values.
*/
{
  FILE *file_out;
  int i;
  int *indexg;
  int j;
  int maxg;
/*
  Open the output file.
*/
  file_out = fopen ( file_out_name, "wt" );

  if ( !file_out )
  {
    fprintf ( stderr, "\n" );
    fprintf ( stderr, "PGMA_WRITE - Fatal error!\n" );
    fprintf ( stderr, "  Cannot open the output file \"%s\".\n", file_out_name );
    exit ( 1 );
  }
/*
  Compute the maximum.
*/
  maxg = 0;
  indexg = g;

  for ( j = 0; j < ysize; j++ )
  {
    for ( i = 0; i < xsize; i++ )
    {
      if ( maxg < *indexg )
      {
        maxg = *indexg;
      }
      indexg = indexg + 1;

    }
  }
/*
  Write the header.
*/
  pgma_write_header ( file_out, file_out_name, xsize, ysize, maxg );
/*
  Write the data.
*/
  pgma_write_data ( file_out, xsize, ysize, g );
/*
  Close the file.
*/
  fclose ( file_out );

  return;
}
/******************************************************************************/

void pgma_write_data ( FILE *file_out, int xsize, int ysize, int *g )

/******************************************************************************/
/*
  Purpose:

    PGMA_WRITE_DATA writes the data for an ASCII PGM file.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    05 June 2010

  Author:

    John Burkardt

  Parameters:

    Input, FILE *FILE_OUT, a pointer to the file.

    Input, int XSIZE, YSIZE, the number of rows and columns of data.

    Input, int *G, the array of XSIZE by YSIZE data.
*/
{
  int i;
  int *indexg;
  int j;
  int numval;

  indexg = g;
  numval = 0;

  for ( j = 0; j < ysize; j++ )
  {
    for ( i = 0; i < xsize; i++ )
    {
      fprintf ( file_out, "%d", *indexg );
      numval = numval + 1;
      indexg = indexg + 1;

      if ( numval % 12 == 0 || i == xsize - 1 || numval == xsize * ysize )
      {
        fprintf ( file_out, "\n" );
      }
      else
      {
        fprintf ( file_out, " " );
      }

    }
  }
  return;
}
/******************************************************************************/

void pgma_write_header ( FILE *file_out, char *file_out_name, int xsize, 
  int ysize, int maxg )

/******************************************************************************/
/*
  Purpose:

    PGMA_WRITE_HEADER writes the header of an ASCII PGM file.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    05 June 2010

  Author:

    John Burkardt

  Parameters:

    Input, FILE *FILE_OUT, a pointer to the file.

    Input, char *FILE_OUT_NAME, the name of the file.

    Input, int XSIZE, YSIZE, the number of rows and columns of data.

    Input, int MAXG, the maximum gray value.
*/
{
  fprintf ( file_out, "P2\n" );
  fprintf ( file_out, "# %s created by PGMA_IO::PGMA_WRITE.\n",
    file_out_name );
  fprintf ( file_out, "%d %d\n", xsize, ysize );
  fprintf ( file_out, "%d\n", maxg );

  return;
}
/******************************************************************************/

void pgma_write_test ( char *file_out_name )

/******************************************************************************/
/*
  Purpose:

    PGMA_WRITE_TEST tests the ASCII PGM write routines.

  Licensing:

    This code is distributed under the GNU LGPL license. 

  Modified:

    05 June 2010

  Author:

    John Burkardt

  Parameters:

    Input, char *FILE_OUT_NAME, the name of the file.
*/
{
  int *g;
  int maxg;
  int xsize;
  int ysize;

  xsize = 300;
  ysize = 300;
/*
  Allocate memory.
*/
  g = ( int * ) malloc ( xsize * ysize * sizeof ( int ) );
/*
  Set the data.
*/
  pgma_example ( xsize, ysize, g );
/*
  Write the data to the file.
*/
  pgma_write ( file_out_name, xsize, ysize, g );

  free ( g );

  return;
}
