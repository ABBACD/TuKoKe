/*
An algorithm for checking prime divisors of polynomials. Made for
comparing the common prime divisors of P_1, P_2, ... , P_n and D.

Running time:
Let S be the sum of degrees of P_i and D. Let the algorithm look for primes
up to N. The running time is
O((S+n)N + N²/log(N))

*/


#include <iostream>
#include <vector>
#include <algorithm>
#include <gmpxx.h>
#include <gmp.h>

using namespace std;

//To prevent overflow issues we will use the mpz_class for big integers
typedef mpz_class ll;
typedef long long l;

//Check primes up to N
const int N = 5e5;

//Maximum amount of polynomials in input
const int M = 5e5;

//True if n is prime, otherwise false
bool pr[N];

//Sieve for primes. Can be shown to have running time O(N * log log N)
void sieve() {
	for(int i = 2; i < N; ++i) {
		if(pr[i]) {
			pr[i] = false;
			continue;
		}
		for(int j = i; j < N; j+=i) {
			pr[j] = true;
		}
	}
}

//Contains the input polynomials in the form a_0 + a_1x + ... + a_dx^d
vector<ll> pol[M];

//val[i][j] is the value of the i:th polynomial at x = j
vector<ll> val[M];

//Calculate the value of the i:th polynomial at value x
ll calc(int i, ll x) {
	ll pow = 1;
	ll ans = 0;
	for(int j = 0; j < pol[i].size(); ++j) {
		ans += pol[i][j]*pow;
		pow *= x;
	}
	return ans;
}

int main() {
	//Sieve for primes
	sieve();


	/*
	Reading the input
	On the first line of the input there should be an integer n, indicating
	there are n+1 polynomials: P_1, P_2, ... , P_n, and D.
	On each of the following n+1 lines there should be:
	an integer d, corresponding to the degree of the next polynomial
	and d + 1 integers, the i:th one corresponding to the coefficient of x^{d - i + 1}
	
	Example: For the polynomials
	P_1(x) = x^2 + 1
	P_2(x) = x^2 - 2
	D(x) = x^4 - 2x^2 + 9
	
	The corresponding input would be

	2
	2 1 0 1
	2 1 0 -2
	4 1 0 -2 0 9

	*/



	int n;

	cin >> n;
	for(int i = 0; i <= n; ++i) {
		int d; cin >> d;
		for(int j = 0; j <= d; ++j) {
			ll co;
			cin >> co;
			pol[i].push_back(co);
		}
		reverse(pol[i].begin(), pol[i].end());
	}

	cout << "I have read the input!\n";

	int amD = 0; //The amount of prime divisors of D so far
	int pi = 0; //The amount of prime numbers so far
	int exp = 0; //The amount of exceptional primes so far

	for(int p = 0; p < N; ++p) {
		if(p%50000 == 0 && p > 0) {
			cout << "\n\n";
			cout << "Calculated statistics for all primes less than " << p << " so far.\n";
			cout << "Amount of prime divisors of D: " << amD << "\n";
			cout << "Amount of primes: " << pi << "\n";
			cout << "Amount of exceptional primes: " << exp << "\n";
			cout << "Density of prime divisors of D: " << (double) amD/pi << "\n";
			cout << "\n\n";
		}
		for(int i = 0; i <= n; ++i) {
			//Calculate values
			val[i].push_back(calc(i, p));
		}
		if(pr[p]) {
			//Check prime divisors

			++pi;
			
			//wP tells if p is a prime divisor of all P_i
			bool wP = true;
			//wD tells if p is a prime divisor of D
			bool wD = false;

			for(int i = 0; i <= n; ++i) {
				//Test if p is a prime divisor of pol[i]
				bool w = false;
				for(int j = 0; j < p; ++j) {
					if(val[i][j]%p == 0) {
						w = true;
						break;
					}
				}
				if(w) {
					if(i == n) {
						wD = true;
						break;
					}
				} else {
					if(i < n) {
						wP = false;
						i = n-1;
					}
				}
			}
			if(wD) {
				++amD;
			}

			if(wP && !wD) {
				++exp;
				cout << p << " is a prime divisor of all P_i, but not a prime divisor of D.\n";
			} else if (!wP && wD) {
				++exp;
				cout << p << " is a prime divisor of D, but not a prime divisor of all P_i.\n";
			}
		}
	}



}
