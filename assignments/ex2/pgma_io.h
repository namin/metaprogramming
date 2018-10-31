# include <stdio.h>

int i4_min ( int i1, int i2 );

void pgma_check_data ( int xsize, int ysize, int maxg, int *garray );
void pgma_example ( int xsize, int ysize, int *garray );

void pgma_read ( char *file_in_name, int *xsize, int *ysize, int *maxg,
       int **garrary );
void pgma_read_data ( FILE *file_in, int xsize, int ysize, int *garray );
void pgma_read_header ( FILE *file_in, int *xsize, int *ysize, int *maxg );
void pgma_read_test ( char *file_in_name );

void pgma_write ( char *file_out_name, int xsize, int ysize, int *garray );
void pgma_write_data ( FILE *file_out, int xsize, int ysize, int *garray );
void pgma_write_header ( FILE *file_out, char *file_out_name, int xsize, 
       int ysize, int maxg );
void pgma_write_test ( char *file_out_name );
