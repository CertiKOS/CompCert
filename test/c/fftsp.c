/*
 C Program: Test_Fast_Fourier_Transform_in_Double_Precision (TFFTDP.c)
 by: Dave Edelblute, edelblut@cod.nosc.mil, 05 Jan 1993
*/

/* Like fft.c, but using single-precision floats */

#include <math.h>
#include <stdlib.h>
#include <stdio.h>

#ifndef PI
double PI=3.14159265358979323846;
#endif

/********************************************************/
/*     A Duhamel-Hollman split-radix dif fft            */
/*     Ref: Electronics Letters, Jan. 5, 1984           */
/*     Complex input and output data in arrays x and y  */
/*     Length is n.                                     */
double FFTSP_GLB_DB1_ZERO = 0.0;

double FFTSP_GLB_DB2 = 2.0;

float FFT_GLB_FLT1 = 3.0f;

double FFT_GLB_DB3 = 1.0;

float FFTSP_GLB_FLT2_HALF = 0.5f;

double FFTSP_GLB_DB5_HALF = 0.5;

double FFTSP_GLB_DB6 = 1e-3;
double FFTSP_GLB_DB_M1 = -1;

/********************************************************/

int dfft(float x[], float y[], int np)
{
  float *px,*py;
  int i,j,k,m,n,i0,i1,i2,i3,is,id,n1,n2,n4;
  float  a,e,a3,cc1,ss1,cc3,ss3,r1,r2,s1,s2,s3,xt,tpi;

  px = x - 1; 
  py = y - 1;
  i = 2; 
  m = 1; 
  
  while (i < np) 
  { 
    i = i+i; 
    m = m+1; 
  }
  
  n = i; 
  
  if (n != np) {
    for (i = np+1; i <= n; i++) {
      px[i] = FFTSP_GLB_DB1_ZERO;
      py[i] = FFTSP_GLB_DB1_ZERO;
    }
    /*printf("nuse %d point fft",n); */
  }

  n2 = n+n;
  tpi = FFTSP_GLB_DB2 * PI;
  for (k = 1;  k <= m-1; k++ ) {
    n2 = n2 / 2; 
    n4 = n2 / 4; 
    e  = tpi / (float)n2; 
    a  = FFTSP_GLB_DB1_ZERO;
    
    for (j = 1; j<= n4 ; j++) {
      a3 = FFT_GLB_FLT1 * a; 
      cc1 = cosf(a); 
      ss1 = sinf(a);
      
      cc3 = cosf(a3); 
      ss3 = sinf(a3); 
      a = e * (float)j; 
      is = j; 
      id = 2 * n2;
	  
      while ( is < n ) {
        for (i0 = is; i0 <= n-1; i0 = i0 + id) {
          i1 = i0 + n4; 
          i2 = i1 + n4; 
          i3 = i2 + n4;
          r1 = px[i0] - px[i2];
          px[i0] = px[i0] + px[i2];
          r2 = px[i1] - px[i3];
          px[i1] = px[i1] + px[i3];
          s1 = py[i0] - py[i2];
          py[i0] = py[i0] + py[i2];
          s2 = py[i1] - py[i3];
          py[i1] = py[i1] + py[i3];
          s3 = r1 - s2; r1 = r1 + s2; 
          s2 = r2 - s1; r2 = r2 + s1;
          px[i2] = r1*cc1 - s2*ss1; 
          py[i2] = FFTSP_GLB_DB_M1*s2*cc1 - r1*ss1;
          px[i3] = s3*cc3 + r2*ss3;
          py[i3] = r2*cc3 - s3*ss3;
        }
        is = 2 * id - n2 + j; 
        id = 4 * id;
      }
    }
  }
  
/************************************/
/*  Last stage, length=2 butterfly  */
/************************************/
  is = 1; 
  id = 4;
  
  while ( is < n) {
    for (i0 = is; i0 <= n; i0 = i0 + id) {
      i1 = i0 + 1; 
      r1 = px[i0];
      px[i0] = r1 + px[i1];
      px[i1] = r1 - px[i1];
      r1 = py[i0];
      py[i0] = r1 + py[i1];
      py[i1] = r1 - py[i1];
    }
    is = 2*id - 1; 
    id = 4 * id; 
  }
  
/*************************/
/*  Bit reverse counter  */
/*************************/
  j = 1; 
  n1 = n - 1;
  
  for (i = 1; i <= n1; i++) {
    if (i < j) {
      xt = px[j];
      px[j] = px[i]; 
      px[i] = xt;
      xt = py[j]; 
      py[j] = py[i];
      py[i] = xt;
    }
    
    k = n / 2; 
    while (k < j) {
      j = j - k; 
      k = k / 2; 
    }
    j = j + k;
  }

/*
  for (i = 1; i<=16; i++) printf("%d  %g   %gn",i,px[i],py[i]);
*/
  
  return(n);
}

/* Test harness */

#define NRUNS 3000

int main(int argc, char ** argv)
{
  int n, np, npm, n2, i, j, nruns;
  float enp, t, y, z, zr, zi, zm, a;
  float * xr, * xi, * pxr, * pxi;

  if (argc >= 2) n = atoi(argv[1]); else n = 12;
  np = 1 << n;
  enp = np; 
  npm = np / 2  - 1;  
  t = PI / enp;
  xr = calloc(np, sizeof(float));
  xi = calloc(np, sizeof(float));
  pxr = xr;
  pxi = xi;
  for (nruns = 0; nruns < NRUNS; nruns++) {
    *pxr = (enp - FFT_GLB_DB3) * FFTSP_GLB_FLT2_HALF;
    *pxi = FFTSP_GLB_DB1_ZERO;
    n2 = np / 2;  
    *(pxr+n2) = FFTSP_GLB_DB_M1*FFTSP_GLB_DB5_HALF;
    *(pxi+n2) = FFTSP_GLB_DB1_ZERO;
    for (i = 1; i <= npm; i++) {
      j = np - i;
      *(pxr+i) = FFTSP_GLB_DB_M1*FFTSP_GLB_DB5_HALF;
      *(pxr+j) = FFTSP_GLB_DB_M1*FFTSP_GLB_DB5_HALF;
      z = t * (float)i;  
      y = FFTSP_GLB_DB_M1*FFTSP_GLB_FLT2_HALF * (cosf(z) / sinf(z));
      *(pxi+i) =  y;
      *(pxi+j) = FFTSP_GLB_DB_M1*y;
    }
    dfft(xr,xi,np);
  }
  zr = FFTSP_GLB_DB1_ZERO;
  zi = FFTSP_GLB_DB1_ZERO;
  npm = np-1;
  for (i = 0; i <= npm; i++ ) {
    a = fabsf(pxr[i] - i);
    if (zr < a) zr = a;
    a = fabsf(pxi[i]);
    if (zi < a) zi = a;
  }
  zm = zr;
  if (zr < zi) zm = zi;
  if (zm < FFTSP_GLB_DB6)
    printf("%d points, result OK\n", np);
  else
    printf("%d points, WRONG result %e\n", np, zm);
  return 0;
}
