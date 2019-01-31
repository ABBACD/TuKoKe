/*
Determines the desired D. Assumes that the input polynomials satisfy the
condition described in the work - otherwise the algorithm does not produce
a polynomial, or it does not necessarily produce a polynomial with the desired
properties.

Contains a slight modification when compared to the original algorithm:
does not do a monic transformation, and therefore may return a non-monic
D. This D is the minimal polynomial of s, multiplied by a suitable constant
to have integer coefficients. Works as expected when input polynomials are
monic.

In addition, the implementation of the algorithm is recursive: it combines
two input polynomials at a time.

Running time: O(T^3), when operations with big numbers are considered O(1).
*/

#include <iostream>
#include <vector>
#include <algorithm>
#include <gmpxx.h>
#include <gmp.h>
using namespace std;

//We shall use mpq_class for handling rational numbers with arbitrarily large
//numerators and denominators.
typedef mpq_class ll;

const int N = 100;

//Contains polynomials, in form a_0 + a_1x + ... + a_nx^n
//Each coefficient is stored in the form a/b, where gcd(a, b) = 1
vector<ll> pol[N];


/*
Input: polynomial p, with leading coefficient != 0
Output: If x is a root of p, return x^deg(p) in terms of x^i with i < deg(p)
*/
vector<ll> calc(vector<ll> p) {
	int deg = p.size() - 1;
	vector<ll> ans;
	ll reci = -1/p[deg];
	for(int i = 0; i < deg; ++i) {
		ans.push_back(reci*p[i]);
	}
	return ans;
}


/*
Input: vector a containing rationals and an integer k 
Output: vector containing elements of a multiplied by k
*/
vector<ll> multi(vector<ll> a, ll k) {
	vector<ll> ans;
	for(int i = 0; i < a.size(); ++i) {
		ans.push_back(k*a[i]);
	}
	return ans;
}


/*
Input: vectors a, b containing rationals. Assume a and b have the same size
Output: vector containing the sum of a[i] and b[i] for all i
*/
vector<ll> add(vector<ll> a, vector<ll> b) {
	vector<ll> ans;
	for(int i = 0; i < a.size(); ++i) {
		ans.push_back(a[i] + b[i]);
	}
	return ans;
}



/*
Parameters: two polynomials a and b.
Output: if x and y are some roots of a and b, 
returns the minimal polynomial of x + y.
*/


vector<ll> extend(vector<ll> a, vector<ll> b) {
	int A = a.size() - 1;
	int B = b.size() - 1;

	//Calculate x^A in terms of x^i for i < A, similarly for y^B
	vector<ll> xA = calc(a);
	vector<ll> yB = calc(b);



	/*
	Calculate powers (x + y)^i for i = 0, 1, ... AB
	Each such polynomial corresponds to a polynomial where the degree
	of x is less than A, and the degree of y is less than B

	The polynomial is stored such that the i:th index contains the coefficient
	x^j * y^k, where j = i%A and k = floor(i/A)

	*/




	vector<ll> power[A*B + 1];
	ll zero (0, 1);
	ll one (1, 1);
	power[0].push_back(one);
	for(int i = 1; i < A*B; ++i) {
		power[0].push_back(zero);
	}

	for(int i = 1; i <= A*B; ++i) {
		/*
		Calculate power[i] by using power[i-1]
		Note that power[i] = power[i-1]*(x + y
		We have to take into consideration the powers of x and y 
		which have exponents equal to A-1 or B-1 in power[i-1].
		
		*/

		for(int j = 0; j < A*B; ++j) {
			power[i].push_back(zero);
		}

		for(int j = 0; j < A*B; ++j) {
			/*
			Go through the terms of power[i-1]
			For each index j, add power[i-1][j]*(x+y) to power[i].
			First add power[i-1][j]*x, then power[i-1][j]*y
			*/

			if((j+1)%A == 0) {
				//We are looking at a power[i-1]'s term with x's exponent A-1
				for(int t = (j/A)*A; t < (j/A)*A + A; ++t) {
					int expX = t - (j/A)*A;
					power[i][t] += xA[expX]*power[i-1][j];
				}	
			} else {
				power[i][j+1] += power[i-1][j];
			}

			if(j/A == B-1) {
				//We are looking at a power[i-1]'s term with y's exponent B-1
				for(int t = j%A; t < A*B; t += A) {
					int expY = t/A;
					power[i][t] += yB[expY]*power[i-1][j];
				}
			} else {
				power[i][j + A] += power[i-1][j];
			}
		}
	}


	/*
	Solve the equation
	q_0*(x+y)^0 + q_1*(x+y)^1 + ... + q_{AB}(x+y)^{AB} = 0
	A non-trivial solution gives the coefficients of the desired polynomial.
	The above equation corresponds to the following system of linear equations:
	q_0p[0][0] + q_1p[1][0] + ... + q_{AB}p[AB][0] = 0
	q_0p[0][1] + q_1p[1][1] + ... + q_{AB}p[AB][1] = 0
	.
	.
	.
	q_0p[0][AB-1] + q_1p[1][AB - 1] + ... + q_{AB}p[AB][AB - 1] = 0

	We use the Gauss-Jordan method for solving this system of linear equations.
	*/	

	//First, we collect the elements of rows into vectors

	vector<ll> row[A*B];

	for(int i = 0; i < A*B; ++i) {
		for(int j = 0; j <= A*B; ++j) {
			row[i].push_back(power[j][i]);
		}
	}

	
	/*
	Solve the system by Gaussian-Jordan
	*/
	
	//r is the row we are currently inspecting
	int r = 0;
	for(int col = 0; col < A*B; ++col) {
		//Column by column turn the matrix into a form with
		//only one non-zero element on each column
		int ind = r;
		
		//Look for a non-zero element on column col
		while(row[ind][col] == 0) {
			++ind;
			if(ind == A*B) {
				break;
			}
		}
		if(ind == A*B) {
			/*
			No non-zero element is found on this column.
			This means that the given system of linear equations does not
			have a unique solution.
			Return that no solution exists.
			*/
			vector<ll> w;
			return w;
		}
		if(ind != r) {
			//Swap rows so that in the end the non-zero elements are on the
			//main diagonal
			swap(row[ind], row[r]);
		}
		//Multiply row r so that the element inspected has value 1
		row[r] = multi(row[r], 1/row[r][col]);
		for(int j = 0; j < A*B; ++j) {
			if(j == r) continue;
			//For all other rows than r turn the element of the column col to 0
			row[j] = add(row[j], multi(row[r], -row[j][col]));
		}
		//Move to the next row
		++r;
	}


	//Return the answer
	vector<ll> ans;

	for(int j = 0; j < A*B; ++j) {
		//The coefficient of x^j
		ans.push_back(-row[j][A*B]);
	}
	//The coefficient of x^(A*B) is 1
	ans.push_back(1);


	return ans;
}


int main() {
	/*
	Reading the input
	On the first line of the input there should be an integer n, the amount of polynomials
	On each of the following n lines there should be:
	an integer d, corresponding to the degree of the next polynomial
	and d + 1 integers, the i:th one corresponding to the coefficient of x^{d - i + 1}
	
	Example: for the two polynomials x^2 + 1 and x^2 - 2 the input would be
	2
	2 1 0 1
	2 1 0 -2

	*/
	int n;
	cin >> n;
	for(int i = 1; i <= n; ++i) {
		int d;
		cin >> d;
		for(int j = d; j >= 0; --j) {
			int a;
			cin >> a;
			ll b (a, 1);
			pol[i].push_back(b);
		}
		reverse(pol[i].begin(), pol[i].end());
	}

	
	vector<ll> D = pol[1];

	for(int j = 2; j <= n; ++j) {
		//Recursively build D
		D = extend(D, pol[j]);
		if(D.size() == 0) {
			//No solution is found
			cout << "The input polynomials do not satisfy the assumption made!\n";
			return 0;
		}
	}

	//Multiply D to get integer coefficients
	for(int i = 0; i < D.size(); ++i) {
		if(D[i].get_den() != 1) {
			D = multi(D, D[i].get_den());
		}
	}


	/*The rest is just printing the output in different formats

	First we print the input and the output polynomial such that it mathces
	the input format of the polynomial prime divisor testing algorithm, to
	make testing easier.

	Then the polynomial D is printed in a format that's easy to read for humans

	After each term there is a new line instead of space - this is because reading
	the input with huge numbers requires new lines between the numbers for some reason
	*/	

	cout << "\n\n\n\n";

	cout << "Machine-readable form: \n\n";

	cout << n << "\n";

	for(int i = 1; i <= n; ++i) {
		cout << pol[i].size() - 1 << "\n";
		for(int j = pol[i].size() - 1; j >= 0; --j) {
			cout << pol[i][j] << "\n";
		}
		cout << "\n";
	}
	cout << D.size() - 1 << "\n";
	for(int i = D.size() - 1; i >= 0; --i) {
		cout << D[i] << "\n";
	}

	cout << "\n\n\n\n\n";

	cout << "Human-readable form: \n\n";


	for(int i = D.size() - 1; i >= 0; --i) {
		if(D[i] == 0) continue;
		if(i < D.size() - 1) {
			if(D[i] > 0) {
				cout << " + ";
			} else {
				cout << " - ";
				D[i] *= -1;
			}
		}
		if(D[i] != 1 || i == 0) {
			cout << D[i];
		}
		if(i > 1) {
			cout << "x^" << i << " ";
		} else if (i == 0) {
			cout << " ";
		} else {
			cout << "x ";
		}
	}

	cout << "\n";
	
}