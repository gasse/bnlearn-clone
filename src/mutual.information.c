
#include "common.h"

/* unconditional mutual information, to be used in C code. */
double c_mi(int *xx, int *llx, int *yy, int *lly, int *num) {

int i = 0, j = 0, k = 0;
int  **n = NULL, *ni = NULL, *nj = NULL;
double res = 0;

  /* initialize the contingency table and the marginal frequencies. */
  n = alloc2dcont(*llx, *lly);
  ni = alloc1dcont(*llx);
  nj = alloc1dcont(*lly);

  /* compute the joint frequency of x and y. */
  for (k = 0; k < *num; k++) {

    n[xx[k] - 1][yy[k] - 1]++;

  }/*FOR*/

  /* compute the marginals. */
  for (i = 0; i < *llx; i++)
    for (j = 0; j < *lly; j++) {

    ni[i] += n[i][j];
    nj[j] += n[i][j];

  }/*FOR*/

  /* compute the mutual information from the joint and marginal frequencies. */
  for (i = 0; i < *llx; i++)
    for (j = 0; j < *lly; j++)
      res += MI_PART(n[i][j], ni[i], nj[j], *num);

  return (res)/(*num);

}/*C_MI*/

/* unconditional mutual information, to be used for the asymptotic test. */
SEXP mi(SEXP x, SEXP y, SEXP lx, SEXP ly, SEXP length) {

int *llx = INTEGER(lx), *lly = INTEGER(ly), *num = INTEGER(length);
int *xx = INTEGER(x), *yy = INTEGER(y);
SEXP result;

  PROTECT(result = allocVector(REALSXP, 1));
  NUM(result) = c_mi(xx, llx, yy, lly, num);
  UNPROTECT(1);

  return result;

}/*MI*/

/* unconditional mutual information, to be used for the asymptotic test. */
SEXP mi_df(SEXP x, SEXP y, SEXP lx, SEXP ly, SEXP length) {

int i = 0, j = 0, k = 0, **n = NULL, *ni = NULL, *nj = NULL;
int *llx = INTEGER(lx), *lly = INTEGER(ly);
int *num = INTEGER(length);
int *xx = INTEGER(x), *yy = INTEGER(y);
double dfx = 0, dfy = 0, *res = NULL;
SEXP result;

  PROTECT(result = allocVector(REALSXP, 2));
  res = REAL(result);
  res[0] = res[1] = 0; // initial test score / degrees of freedom

  /* initialize the contingency table and the marginal frequencies. */
  n = alloc2dcont(*llx, *lly);
  ni = alloc1dcont(*llx);
  nj = alloc1dcont(*lly);

  /* compute the joint frequency of x and y. */
  for (k = 0; k < *num; k++) {

    n[xx[k] - 1][yy[k] - 1]++;

  }/*FOR*/

  /* compute the marginals. */
  for (i = 0; i < *llx; i++)
    for (j = 0; j < *lly; j++) {

		ni[i] += n[i][j];
		nj[j] += n[i][j];

	}/*FOR*/

  /* heuristic to compute the degree of freedom */
  dfx = (*llx - 1);
  dfy = (*lly - 1);
  for (i = 0 ; i < *llx; i++) {
    if (ni[i] == 0) dfx--;
  }/*FOR*/
  for (j = 0 ; j < *lly; j++) {
    if (nj[j] == 0) dfy--;
  }/*FOR*/
  if (dfx < 0) dfx = 0;
  if (dfy < 0) dfy = 0;

  /* compute the mutual information from the joint and marginal frequencies. */
  for (i = 0; i < *llx; i++)
    for (j = 0; j < *lly; j++)
      res[0] += MI_PART(n[i][j], ni[i], nj[j], *num);

  res[0] = (res[0])/(*num);
  res[1] = dfx * dfy;

  UNPROTECT(1);

  return result;

}/*MI_DF*/

/* conditional mutual information, to be used for the asymptotic test. */
SEXP cmi(SEXP x, SEXP y, SEXP z, SEXP lx, SEXP ly, SEXP lz, SEXP length) {

int i = 0, j = 0, k = 0, ***n = NULL, **ni = NULL, **nj = NULL, *nk = NULL;
int *llx = INTEGER(lx), *lly = INTEGER(ly), *llz = INTEGER(lz);
int *num = INTEGER(length);
int *xx = INTEGER(x), *yy = INTEGER(y), *zz = INTEGER(z);
double *res = NULL;
SEXP result;

  /* allocate and initialize result to zero. */
  PROTECT(result = allocVector(REALSXP, 1));
  res = REAL(result);
  *res = 0;

  /* initialize the contingency table and the marginal frequencies. */
  n = alloc3dcont(*llx, *lly, *llz);
  ni = alloc2dcont(*llx, *llz);
  nj = alloc2dcont(*lly, *llz);
  nk = alloc1dcont(*llz);

  /* compute the joint frequency of x, y, and z. */
  for (k = 0; k < *num; k++) {

    n[xx[k] - 1][yy[k] - 1][zz[k] - 1]++;

  }/*FOR*/

  /* compute the marginals. */
  for (i = 0; i < *llx; i++)
    for (j = 0; j < *lly; j++)
      for (k = 0; k < *llz; k++) {

        ni[i][k] += n[i][j][k];
        nj[j][k] += n[i][j][k];
        nk[k] += n[i][j][k];

      }/*FOR*/

  /* compute the conditional mutual information from the joint and
     marginal frequencies. */
  for (i = 0; i < *llx; i++)
    for (j = 0; j < *lly; j++)
      for (k = 0; k < *llz; k++)
        *res += MI_PART(n[i][j][k], ni[i][k], nj[j][k], nk[k]);

  *res = (*res)/(*num);

  UNPROTECT(1);

  return result;

}/*CMI*/

/* conditional mutual information, to be used for the asymptotic test. */
SEXP cmi_df(SEXP x, SEXP y, SEXP z, SEXP lx, SEXP ly, SEXP lz, SEXP length) {

int i = 0, j = 0, k = 0, ***n = NULL, **ni = NULL, **nj = NULL, *nk = NULL;
int *llx = INTEGER(lx), *lly = INTEGER(ly), *llz = INTEGER(lz);
int *num = INTEGER(length);
int *xx = INTEGER(x), *yy = INTEGER(y), *zz = INTEGER(z);
double *res = NULL, df = 0, dfx = 0, dfy = 0;
SEXP result;

  PROTECT(result = allocVector(REALSXP, 2));
  res = REAL(result);
  res[0] = res[1] = 0; // test score / degrees of freedom

  /* initialize the contingency table and the marginal frequencies. */
  n = alloc3dcont(*llx, *lly, *llz);
  ni = alloc2dcont(*llx, *llz);
  nj = alloc2dcont(*lly, *llz);
  nk = alloc1dcont(*llz);

  /* compute the joint frequency of x, y, and z. */
  for (k = 0; k < *num; k++) {

    n[xx[k] - 1][yy[k] - 1][zz[k] - 1]++;

  }/*FOR*/

  /* compute the marginals. */
  for (i = 0; i < *llx; i++)
    for (j = 0; j < *lly; j++)
      for (k = 0; k < *llz; k++) {

        ni[i][k] += n[i][j][k];
        nj[j][k] += n[i][j][k];
        nk[k] += n[i][j][k];

      }/*FOR*/

  /* heuristic to compute the degree of freedom */
  df = 0;
  for (k = 0; k < *llz; k++) {
    dfx = (*llx - 1);
    dfy = (*lly - 1);
    for (i = 0 ; i < *llx; i++) {
      if (ni[i][k] == 0) dfx--;
    }/*FOR*/
    for (j = 0 ; j < *lly; j++) {
      if (nj[j][k] == 0) dfy--;
    }/*FOR*/
    if (dfx < 0) dfx = 0;
    if (dfy < 0) dfy = 0;
    df += dfx * dfy;
  }/*FOR*/

  /* compute the conditional mutual information from the joint and
     marginal frequencies. */
  for (i = 0; i < *llx; i++)
    for (j = 0; j < *lly; j++)
      for (k = 0; k < *llz; k++)
        res[0] += MI_PART(n[i][j][k], ni[i][k], nj[j][k], nk[k]);

  res[0] = (res[0])/(*num);
  res[1] = df;

  UNPROTECT(1);

  return result;

}/*CMI_DF*/

/* unconditional Gaussian mutual information, to be used in C code. */
double c_mig(double *xx, double *yy, int *num) {

double cor = c_fast_cor(xx, yy, num);

  return - 0.5 * log(1 - cor * cor);

}/*C_MIG*/

/* unconditional Gaussian mutual information, to be used in the asymptotic test. */
SEXP mig(SEXP x, SEXP y, SEXP length) {

double *xx = REAL(x), *yy = REAL(y);
int *num = INTEGER(length);
SEXP result;

  PROTECT(result = allocVector(REALSXP, 1));
  NUM(result) = c_mig(xx, yy, num);
  UNPROTECT(1);

  return result;

}/*MIG*/
