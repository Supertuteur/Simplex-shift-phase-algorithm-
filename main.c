/**
 * Simplex algorithm as presented in "Finite mathematics and applied calculus".
 * 
 * @author Jean-François Dollinger
 */

#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#include <limits.h>

#define VERBOSE

#define error(msg, errno) error_f(msg, errno, __LINE__)

void error_f(char *, int, int);
void error_f(char *s, int errno, int ln) {
  fprintf(stderr, "Error (%d) : %s, at line %d.", errno, s, ln);
  exit(errno);
}

/**
 * Rational related constructions.
 * */
 
int pgcd(int a, int b);
 
typedef struct rational {
  int a;
  int b;
} rational;

rational rmax = { a: INT_MAX, b: 1 };
#define RATIONAL_MAX rmax

rational rnull = { a: 0, b: 1 };
#define RATIONAL_NULL rnull

void show(rational *r, int *bs, int m, int n);

static inline rational to_rational(int a);
static inline rational init_rational(int a, int b);
static inline rational rational_normalize(rational r0);
static inline rational rational_plus(rational r0, rational r1);
static inline rational rational_minus(rational r0, rational r1);
static inline rational rational_mult(rational r0, rational r1);
static inline rational rational_int_mult(rational r0, int s);
static inline rational rational_div(rational r0, rational r1);
static inline bool is_rational_negative(rational r0);
static inline bool is_rational_negative_or_null(rational r0);
static inline bool is_rational_null(rational r0);
static inline bool is_rational_greater_equal(rational r0, rational r1);
static inline bool is_rational_lower_equal(rational r0, rational r1);
static inline bool is_rational_greater(rational r0, rational r1);
static inline bool is_rational_lower(rational r0, rational r1);
static inline int rational_cmp(rational r0, rational r1);
static inline double rational_solve(rational r0);
static inline rational rational_simplify(rational r0);
void rational_show(rational r0);

/**
 * Simplex related constructions.
 * */
 
typedef enum {
  OPTIMUM = 0,
  UNBOUND_PB,
  FEASIBLE_PB,
  INFEASIBLE_PB,
} simplex_rcd;

const char* simplex_rcd_msg[] =
{
    "optimum found",
    "unbound problem",
    "feasible problem",
    "infeasible problem"
};

typedef enum {
  LT_EQUAL = 0,
  GT_EQUAL,
  EQUAL,
  OBJ,
  BINOP_MAX //ONLY to check values
} binop;


void get_canonical_mx_size(int *m0, int *n0, binop *o, int m, int n);
void to_canonical(rational *r0, int m0, int n0, rational *r1, int m1, int n1, binop *o);
void initial_basic_solution(int *bs, int m, int n);
void get_basic_solution(rational *r, int *bs, int m, int n);
int test_ratio(rational *r, int m, int n, int pc);
int get_pivot_column(rational *r, int n);
void elimination_step(rational *r, int m, int n, int pl, int pc);
simplex_rcd simplex(rational *r, int m, int n, binop *o);
void show(rational *r, int *bs, int m, int n);

void print_rational_matrix(rational *r, int m, int n);
simplex_rcd phase1(rational *r, int *bs, int m, int n);
simplex_rcd phase2(rational *r, int *bs, int m, int n);






#define is_rational_not_null(rt) (rt.a != 0)

static inline rational to_rational(int a) {
  rational r = { a, 1 };
  
  return r;
}

static inline rational init_rational(int a, int b) {
  rational r = { a: a, b: b };
  
  return rational_normalize(r);
}

/**
 * Subject to overflows due to multiplication.
 * */
static inline rational rational_normalize_0(rational r0) {
  rational r1 =  { a: r0.a * r0.b, b: r0.b * r0.b };
  
  return r1;
}

static inline rational rational_normalize(rational r0) {
  int s = 1;
  
  if(r0.a < 0) {
    s = -1;
    r0.a = -r0.a;
  }
  if(r0.b < 0) {
    s = -s;
    r0.b = -r0.b;
  }
  r0.a = s * r0.a;
  
  return r0;
}

static inline rational rational_plus(rational r0, rational r1) {
  rational r = { a : (r0.a * r1.b) + (r1.a * r0.b), b : r0.b * r1.b };
  
  r = rational_simplify(r);

  return r;
}

static inline rational rational_minus(rational r0, rational r1) {
  rational r2 = {a: -r1.a, b: r1.b };
  
  return rational_simplify(rational_plus(r0, r2));
}

static inline rational rational_mult(rational r0, rational r1) {
  rational r = { a:r0.a * r1.a, b:r0.b * r1.b };
  
  r = rational_simplify(r);
  
  return r;
}

static inline rational rational_int_mult(rational r0, int s) {
  rational r = { a:r0.a * s, b:r0.b };
  
  r = rational_simplify(r);
  
  return r;
}

static inline rational rational_div(rational r0, rational r1) {
  rational r2 = {a: r1.b, b: r1.a };
  
  r2 = rational_mult(r0, r2);
  r2 = rational_simplify(r2);
  
  return r2;
}

static inline bool is_rational_negative(rational r0) {
  return (r0.a < 0 ^ r0.b < 0);
}

static inline bool is_rational_negative_or_null(rational r0) {
  return (r0.a <= 0 ^ r0.b < 0);
}

static inline bool is_rational_positive_not_null(rational r0) {
  return !is_rational_negative_or_null(r0);
}

static inline bool is_rational_null(rational r0) {
  return r0.a == 0;
}

static inline bool is_rational_greater_equal(rational r0, rational r1) {
  
  return (r0.a * r1.b) >= (r1.a * r0.b);
}

static inline bool is_rational_lower_equal(rational r0, rational r1) {
  return (r0.a * r1.b) <= (r1.a * r0.b);
}

static inline bool is_rational_greater(rational r0, rational r1) {
  return (r0.a * r1.b) > (r1.a * r0.b);
}

static inline bool is_rational_lower(rational r0, rational r1) {
  return (r0.a * r1.b) < (r1.a * r0.b);
}

/**
 * 
 * @return r0 < r1 ? -1 : r0 == r1 ? 0 : 1;
 * */
static inline int rational_cmp(rational r0, rational r1) {
  int rt1, rt2;
  
  rt1 = r0.a * r1.b;
  rt2 = r1.a * r0.b;
  
  return rt1 < rt2 ? -1 : rt1 == rt2 ? 0 : 1;
}

static inline double rational_solve(rational r0) {
  return r0.a / r0.b;
}

int pgcd(int a, int b) {
  int t;
  
  for(; b != 0;) {
    t = a % b;
    a = b;
    b = t;
  }
  
  return a;
}

static inline rational rational_simplify(rational r0) {
  int pgcd0 = pgcd(r0.a, r0.b);
  rational r1 = { a:r0.a / pgcd0, b:r0.b / pgcd0 };
  
  r1 = rational_normalize(r1);
  
  return r1;
}

void rational_show(rational r0) {
  printf("%d / %d\n", r0.a, r0.b);
}

void print_rational(rational r) {
  printf("%d/%d\t", r.a, r.b);
  /*if(r.b != 1) {
    printf("%d/%d\t", r.a, r.b);
  }
  else {
    printf("%d\t", r.a);
  }*/
}

void print_rational_matrix(rational *r, int m, int n) {
  int i, j;
  
  for(i = 0; i < m; ++i) {
    for(j = 0; j < n; ++j) {
      print_rational(r[i * n + j]);
    }
    printf("\n");
  }
  printf("\n");
}

void get_canonical_mx_size(int *m0, int *n0, binop *o, int m, int n) {
  int i;
  
  int sz0[4] = {0, 0, 1, 0};
  
  *m0 = m;
  *n0 = n;
  
  if(n > 0 && m > 0) {
    *n0 += 1; //inc by 1 due to m - 1 in the loop.
    for(i = 0; i < m - 1; ++i) {
      *m0 += sz0[(int)o[i]];
      (*n0)++;
    }  
  }
}


/**
 * Transforms a linear system with mixed constraints into its corresponding canonical form (system of linear equations including slack and surplus variables) :
 * - Ensures the positiveness of the constants.
 * - Adds the adequate slack (<= constraint) or surplus variables (>= constraint). Transforms equality into a comparable system of inequations.
 * */
void to_canonical(rational *r0, int m0, int n0, rational *r1, int m1, int n1, binop *o) {
  int i, j, k, l;
  rational rt[4] = { {1, 1}, {-1, 1}, {1, 1}, {-1, 1} };
  binop cpy[4] = { 1, 1, 2, 1 };
  
  //table containing operator inversion in case of multiplication by -1
  binop inv[4] = { GT_EQUAL, LT_EQUAL, EQUAL, OBJ };
  
  //constant must be positive, if not multiply row by -1.
  for(i = 0; i < m1 - 1; ++i) {
    if(is_rational_negative(r1[n1 * (i + 1) - 1])) {
      for(j = 0; j < n1; ++j) {
        r1[n1 * i + j] = rational_int_mult(r1[n1 * i + j], -1);
      }
      o[i] = inv[o[i]];
    }
  }
  
  /*Convert to canonical form.
   * Introduce slack variable (positive) for <= inequality.
   * Introduce surplus variable (négative) for >= inequality.
   * Convert equation into comparable system of inequations.
  */
  for(i = 0, k = 0; i < m1; ++i) {
    l = k + cpy[o[i]];
    for(; k < l; ++k) {
      for(j = 0; j < n1 - 1; ++j) {
        r0[k * n0 + j] = r1[i * n1 + j];
      }
      r0[k * n0 + (n0 - 1)] = r1[i * n1 + j];
      
      for(j = 0; j < m1; ++j) {
        r0[k * n0 + (n1 - 1 + j)] = k == j ? rt[o[i] + (l - k) - 1] : RATIONAL_NULL;
      }
    }
  }
}

void initial_basic_solution(int *bs, int m, int n) {
  int i;
  
  for(i = 0; i < m - 1; ++i) {
    bs[i] = (n - 1) + i;
  }
}

/**
 * Seeks for current basic variables. Unused ATM.
 * */
void get_basic_solution(rational *r, int *bs, int m, int n) {
  int i, j;
  
  int last;
  int ok[n - 1], ln[n - 1];
  
  //init
  for(i = 0; i < n - 1; ++i) {
    ok[i] = 0;
  }
  
  for(i = 0; i < m - 1; ++i) {
    for(j = 0; j < n - 1; ++j) {
      if(is_rational_not_null(r[i * n + j])) {
        ok[j] += 1;
        ln[j] = i;
      }
    }
  }
  
  for(i = 0; i < n - 1; ++i) {
    if(ok[i] == 1) {
      bs[ln[i]] = i;
    }
  }
}

/**
 * Performs a test ratio. Returns the most restricting line ; this ensures the validity of the basic solution. 
 * */
int test_ratio(rational *r, int m, int n, int pc) {
  int i, j;
  
  int pl = -1;
  rational rt0, rt1, rt2;
  
  /**
   * Get first legal (i.e. coefficient must be strictly greater than 0) pivot line candidate in a loop unswitching fashion. 
   * 
   * This avoids using RATIONAL_MAX which can potentially overflow when performing rational operations.
   * */
  for(i = 0; i < m - 1; ++i) {
    rt2 = r[i * n + pc];
    
    if(is_rational_positive_not_null(rt2)) {
      rt0 = rational_div(r[i * n + n - 1], rt2);
      pl = i;
      
      break;
    }
  }
  
  for(i = i + 1; i < m - 1; ++i) {
    rt2 = r[i * n + pc];

    if(is_rational_positive_not_null(rt2)) {
      rt1 = rational_div(r[i * n + n - 1], rt2);

      if(is_rational_lower(rt1, rt0)) {
        rt0 = rt1;
        pl = i;
      }
    }
  }
  
  return pl;
}

int get_pivot_column(rational *r, int n) {
  int j;
  
  int pc = 0;
  
  //look for pivot column in the n - 1 columns
  for(j = 1; j < n - 1; ++j) {
    if(is_rational_greater(r[j], r[pc])) {
      pc = j;
    }
  }
  
  if(is_rational_negative_or_null(r[pc])) {
    pc = -1;
  }
  
  return pc;
}

/**
 * Pivots the linear system of equation. See Gauss-Jordan algorithm.
 * */
void elimination_step(rational *r, int m, int n, int pl, int pc) {
  int i, j;
  rational coeff, pivot;
  
  pivot = r[pl * n + pc];
  for(j = 0; j < n; ++j) {
    r[pl * n + j] = rational_div(r[pl * n + j], pivot);
  }

  for(i = 0; i < m; ++i) {
    coeff = r[i * n + pc];
    for(j = 0; j < n; ++j) {
      if(i != pl) {
        r[i * n + j] = rational_minus(r[i * n + j], rational_mult(coeff, r[pl * n + j]));
      }
    }
  }
  
}

/**
 * Transforms the system of linear equations, so that we start with a valid basic solution.
 * */
simplex_rcd phase1(rational *r, int *bs, int m, int n) {
  int i;
  int pc, pl;

  for(i = 0; i < m - 1; ++i) {
    //redo as long as the considered basic variable is negative
    while(is_rational_lower(r[i * n + bs[i]], RATIONAL_NULL)
            && !is_rational_null(r[i * n + (n - 1)])) {
      
      if((pc = get_pivot_column(&r[i * n], n)) == -1) {
        //stop the algorithm as there is no solution.
        return INFEASIBLE_PB;
      }
  
      if((pl = test_ratio(r, m, n, pc)) == -1) {
        //stop the algorithm as there is no solution.
        return INFEASIBLE_PB;
      }
      
      elimination_step(r, m, n, pl, pc);
      
      //change basic/non-basic
      bs[pl] = pc;
    }
  }
  
  #ifdef VERBOSE
  printf("----- Phase 1 : Matrix with feasible initial solution. -----\n");
  print_rational_matrix((rational *)r, m, n);
  #endif
  
  return FEASIBLE_PB;
}
/**
 * Performs simplex algorithm.
 * */
simplex_rcd phase2(rational *r, int *bs, int m, int n) {
  int pc, pl;
  #ifdef VERBOSE
  printf("----- Phase 2 : Compute solution. -----\n");
  #endif
  for(;;) {
    if((pc = get_pivot_column(&r[(m - 1) * n], n)) == -1) {
      //stop the algorithm as a solution was found. Fetch basic solution in bs.
      return OPTIMUM;
    }
    /**
     * Check if unbound polyhedron.
     * */ 
    if((pl = test_ratio(r, m, n, pc)) == -1) {
      return UNBOUND_PB;
    }
    
    #ifdef VERBOSE
    printf("Pivoting on [%d][%d]\n", pl, pc);
    #endif
    
    elimination_step(r, m, n, pl, pc);
      
    //change basic/non-basic
    bs[pl] = pc;
    
    #ifdef VERBOSE
    print_rational_matrix((rational *)r, m, n);
    #endif
  }
}

/**
 * Two phase simplex algorithm which handles maximisation problems. For minimization, compute dual form.
 * - Phase 1, transforms the system of linear equations, so that we start with a valid basic solution. 
 * - Phase 2, performs simplex standard maximisation algorithm.
 * */
simplex_rcd simplex(rational *r, int m, int n, binop *o) {
  int i, j;
  
  int n0, m0;
  get_canonical_mx_size(&m0, &n0, o, m, n);
  
  rational rr[m0][n0];
  rational *rp = (rational *)rr;
  
  /**
  * TODO : transform to maximisation problem first.
  */
  to_canonical(rp, m0, n0, r, m, n, o);
  print_rational_matrix(rp, m0, n0);
  
  int bs[m0];
  
  /**
   * Initialize the bs array, which points to the set of basic variables.
   * */
  get_basic_solution(rp, bs, m0, n0);
  /**
   * Apply phase 1 & 2 of the simplex method to compute optimum.
  */
  simplex_rcd sx_cde;
  if((sx_cde = phase1(rp, bs, m0, n0)) == FEASIBLE_PB) {
    sx_cde = phase2(rp, bs, m0, n0);
  }
  
  //Print solution according to current basic solution (bs).
  switch((int)sx_cde) {
    case OPTIMUM:
      show(rp, bs, m0, n0);
      break;
    default:
      
      fprintf(stderr, "Computation returned error (%d): %s.\n", (int)sx_cde, simplex_rcd_msg[sx_cde]);
      break;
  }
  
  return sx_cde;
}


void show(rational *r, int *bs, int m, int n) {
  int i;
  
  rational rt0, rt[n - 1];
  
  //init.
  for(i = 0; i < n - 1; ++i) {
    rt[i] = RATIONAL_NULL;
  }
  
  for(i = 0; i < m - 1; ++i) {
    rt0 = rational_div(r[i * n + (n - 1)], r[i * n + bs[i]]);
    rt[bs[i]] = rt0;
  }
  
  for(i = 0; i < n - 1; ++i) {
    printf("%d: ", i);
    print_rational(rt[i]);
  }
}

/*
In a general 
*/





/*#define M 4
#define N 4*/

/*#define M 4
#define N 3*/

/*#define M 5
#define N 3*/

#define M 5
#define N 10


 
/**
 * Reads an augmented matrix from stream.
 * - Bottom line specifies the objective function.
 * - Left column specifies the operator (<=, >=, =).
 * - Right column specifies the affine equations constant.
 * Note that this matrix format suits the polylib format:
 * #nb_rows nb_cols
 * #nb_rows *
 * #          <=(0)/>=(1)/=(2)/objective(3)  [ coef_i ]*  constant
 * 
 * Careful, b and r pointers must be freed after computation.
 * */
void read(FILE *s, binop **b, rational **r, int *m, int *n) {
  int i, j, v, w, ntok;
  char c0;
  
  if(s == NULL) { goto error0; }

  //get the matrix size
  ntok = fscanf(s, "%d%d", m, n);
  
  if(ntok != 2 || (*m < 0 || *n < 0)) {
    goto error1;
  }
  
  if((*b = (binop *)malloc(sizeof(binop) * (*m))) == NULL) {
    goto error2;
  }
  
  *n = *n - 1;
  if((*r = (rational *)malloc(sizeof(rational) * (*m) * (*n))) == NULL) {
    goto error3;
  }

  for(i = 0; i < (*m); ++i) {
    ntok = fscanf(s, "%d", &((*b)[i]));
    if(ntok != 1 || ((*b)[i] < 0 || (*b)[i] >= BINOP_MAX)) {
      goto error4;
    }
    for(j = 0; j < (*n); ++j) {
      ntok = fscanf(s, "%d/%d", &v, &w, &c0);
      switch(ntok) {
        case 1:
          (*r)[i * (*n) + j] = to_rational(v);
          break;
        case 2:
          (*r)[i * (*n) + j] = init_rational(v, w);
          break;
        default:
          goto error4;
      }
    }
  }
  
  return;
  
  //error handling - error() exits program
  error0:
    error("input failure : null file handler", EXIT_FAILURE);

  error3:
    free(*b);
  error2:
    error("memory failure : allocation failed", EXIT_FAILURE);

  error4:
    free(*r);
    free(*b);
  error1:
    error("input failure : incorrect input matrix format", EXIT_FAILURE);
}

 
int main(void) {
  /*
   * Possible input (for more see read function documentation) : 
5 5
0 3 1 3 80
1 -1 4 3 20
1 -1 -1 3 20
1 5 8 2 30
3 -5 -2 -2 0
   * 
4 5
1 1 -1 3 10
0 4 3 1 3
1 2 -1 3 15
3 5 -5 1 0
   *
3 4
1 1 0 40
1 0 1 10
3 2 -3 0
   * 
   * 
   * 
   * 
   * 
   * */
  
  /*binop op[M] = {LT_EQUAL, LT_EQUAL, GT_EQUAL, OBJ};
  rational rread[M][N] = { { { 1, 1 }, { 1, 1 }, { 1, 1 }, { 100, 1 } }
                        , { { 4, 1 }, { 10, 1 }, { 7, 1 }, { 480, 1 } }
                        , { { 1, 1 }, { 1, 1 }, { 1, 1 }, { 60, 1 } }
                        , { { 4, 1 }, { 12, 1 }, { 6, 1 }, { 0, 1 } } };*/
                        
  /*binop op[M] = {LT_EQUAL, LT_EQUAL, LT_EQUAL, OBJ};
  rational rread[M][N] = { { { 1, 1 }, { 1, 1 }, { 100, 1 } }
                        , { { 1, 2 }, { -1, 2 }, { 0, 1 } }
                        , { { 4, 5 }, { 1, 5 }, { 0, 1 } }
                        , { { 35, 1 }, { 25, 1 }, { 0, 1 } } };*/
  
  /*binop op[M] = {LT_EQUAL, LT_EQUAL, LT_EQUAL, GT_EQUAL, OBJ};
  rational rread[M][N] = { { { 1, 1 }, { 1, 1 }, { 21000, 1 } }
                        , { { 1, 1 }, { 0, 1 }, { 13000, 1 } }
                        , { { 0, 1 }, { 1, 1 }, { 6000, 1 } }
                        , { { 1, 1 }, { -2, 1 }, { 0, 1 } }
                        , { { 1, 10 }, { 8, 100 }, { 0, 1 } } };*/
                        
  /*binop op[M] = {LT_EQUAL, LT_EQUAL, LT_EQUAL, EQUAL, OBJ};
  rational rread[M][N] = 
{ 
{ { 20, 1 }, { 50, 1 }, { 30, 1 }, { 30, 1 }, { 60, 1 }, { 40, 1 }, { 40, 1 }, { 10, 1 }, { 10, 1 }, { 3000, 1 } },
{ { 30, 1 }, { 40, 1 }, { 20, 1 }, { 40, 1 }, { 30, 1 }, { 30, 1 }, { 50, 1 }, { 30, 1 }, { 10, 1 }, { 3000, 1 } },
{ { 50, 1 }, { 10, 1 }, { 50, 1 }, { 30, 1 }, { 40, 1 }, { 10, 1 }, { 10, 1 }, { 60, 1 }, { 80, 1 }, { 4000, 1 } },
{ { 1, 1 }, { 1, 1 }, { 1, 1 }, { 1, 1 }, { 1, 1 }, { 1, 1 }, { 1, 1 }, { 1, 1 }, { 1, 1 }, { 100, 1 } },
{ { 73, 10 }, { 69, 10 }, { 73, 10 }, { 75, 10 }, { 76, 10 }, { 6, 1 }, { 58, 10 }, { 43, 10 }, { 41, 10 }, { 0, 1 } }
};*/

  binop *op;
  rational *rread;
  
  int m0, n0;

  read(stdin, &op, &rread, &m0, &n0);
  
  simplex((rational *)rread, m0, n0, op);
  

  free(op);
  free(rread);
  
  return EXIT_SUCCESS;
}



