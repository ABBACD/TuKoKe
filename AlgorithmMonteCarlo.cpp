/*
Determines the desired D. Assumes that the input polynomials satisfy the
condition described in the work - otherwise the algorithm does not produce
a polynomial in a finite amount of steps, or it does not necessarily produce 
a polynomial with the desired properties.

Since the desired D may have very large coefficients, the original algorithm
uses a lot of time to calculate with big integers. The amount of calculations
used with big integers can be significantly reduced. This is achieved by
determining the coefficients of D modulo many distinct prime numbers, and updating
the answer by combining the old and new information by the Chinese Remainder 
Theorem. The only step where big integers are handled is the combination term,
compared to  the original algorithm using big integers for solving the 
system of linear equations.

One can not determine the coefficients of D modulo all primes, but there
are only finitely many non-working primes which we have to discard. This will
be discussed in more detail later.

The main issue is determining the needed amount of primes, in other words, 
giving a bound on the size of the absolute values of D's coefficients.
I was not able to give a bound for the coefficients, but I proved a bound
for the size of the coefficients in the system of linear equations. In 
pracite the size of D's coefficients is of the same magnitude.

Therefore, this is a Monte-Carlo algorithm - it does not necessarily produce
a correct answer always. However, the probability of an incorrect mistake is
very small. In the example given later, with T = 100, a heuristic approximation
gives the probability for an error to be 10^(-500).

The bound on the coefficients of the system of linear equations is as follows:

Let n be the amount of input polynomials.
Let m_i be the maximum value of the absolute value of the coefficients of the
input polynomial P_i.
The maximum value of the absolute value of the coefficients of s^j, when
written in terms of the natural basis B, is at most

(n + m_1 + m_2 + ... + m_n)^j

The idea of the proof is to prove the bound on induction with respect to j.
Case j = 0 is trivial. For the induction step one can split into two cases
as in the proof of lemma 20 and use triangle inequality.

Therefore, the coefficients of the equations are at most

(n + m_1 + ... + m_n)^T                   (1)

where T is the product of the input polynomials' degrees.

This gives an approximation for the amount of primes needed. If we use
the primes p_1, p_2, ... , p_k, we want that their product is of the same
size as the bound (1), that is,

p_1p_2 ... p_k >= (n + m_1 + ... + m_n)^T       (2)

Taking natural logarithms from both sides of the inequality (2) we have

log(p_1) + log(p_2) + ... + log(p_k) >= T * log(n + m_1 + ... + m_n)    (3)

If p_1, p_2, ... , p_k are the smallest k primes in order, the left hand
side is equal to the Chebyshev's (first) function. This has a well-known approximaion,
the left hand side is of the magnitude p_k. See for example the paper
Estimates of Some Functions Over Primes without R.H.
by Pierre Dusart (published to Arxiv on 2 Feb 2010), link:
https://arxiv.org/abs/1002.0442 (retrieved 14 Jan 2019)

Therefore, we want

p_k >= T * log(n + m_1 + ... + m_n)      (4)

In practice, T is at mostsome hundreds (as the algorithm has running time O(T^3)), and
(4) gives a reasonable bound.

Instead of picking just small primes, one can choose large primes for the
moduli instead. This gives a better running time, as less primes have to
be checked. The primes used in the algorithm all have size of at least 10^5.

There is a risk that the coefficients of the outputted answer is incorrect.
However, the product of the primes for which we calculate the coefficients
have a size of at least (n + m_1 + ... + m_n)^T, as in (2). Also, in the
algorithm it is checked that the next couple primes give the same answer
as those before, so even if the bound did not work, we would have a very
small chance of error.

For example, assume we have a input where T = 100.
Assume that the answer D_answer is incorrect, and we check our
answer with an extra prime p_extra of size 10^5. If the answer changes, that is,
the coefficients of D_correct (modulo p_extra) do not all match with the
coefficients of D_answer (modulo p_extra), we note that there is an error, and
check the answer with more primes. If the answer does not change, we return
D_answer.

The probability of not noticing the error can be roughly estimated by assuming
that the coefficients of D_answer are random variables. The probability of the
constant terms of D_answer and D_correct matching modulo p_extra can be estimated
as 1/p_extra. For the probability of all coefficients matching mod p_extra
has therefore probability of (1/p_extra)^T, in this case equal to 10^(-500). One
can even further decrease the probability of error by checking the answer
with multiple extra primes.

Then, for the fact that we can calculte the coefficients modulo for all
but finitely many primes. The idea is as follows:

Think of the process of solving the system of linear equations.
We multiply/divide equations, and add/subtract them from each other
The only problematic step is division. However, there are only finitely
many primes that divide some numer x that we divide an equation by. For
all other primes we can solve the system in modulo p just as we would solve
it in the rational numbers. Because the system has a unique solution in
rationals (up to multiplyinh by a cosntant), it has a unique solution in
integers modulo p.

In practice there are not that many not-working primes, and they are usually
very small. If we try to solve the system mod p for only large p, this
is rarely a problem.


As an example of how large coefficients the answer might have, test the
algorithm with the following input.

7
2 1 -691199 -795187
2 1 -224057 -191899
2 1 -534637 -147163
2 1 -665803 -166741 
2 1 -358867 -332201 
2 1 -521009 -746989
2 1 -364223 -637603


Biggest coefficients have size of around 10^800. 
Expected running time for this input is about 10 seconds.


Running time:
Let T be the product of the input polynomials.
Let B = T*log(n + m_1 + ... + m_n), as described above.
The running time is O(T^3 * B), assuming the bound* given for the
size of the coefficients of the answer holds.

*That is, the size of each coefficient is at most e^B

In practice the constant term of the O-term is small, as only big primes
are used for calculations, and this algorithm is faster than the regular
algorithm when the input is big.


*/

#include <iostream>
#include <vector>
#include <algorithm>
#include <gmpxx.h>
#include <gmp.h>
#include <math.h>

using namespace std;

//To prevent overflow issues we will use the mpz_class for big integers
typedef mpz_class lll;
typedef long long ll;
typedef pair<ll, ll> pll;
#define F first
#define S second

//Maximum amount of polynomials
const int N = 100;

//Check for primes up to M if necessary
const int M = 6e5 + 5;

//Check for primes of size at least C
const int C = 5e5 + 5;

//Contains polynomials, in form a_0 + a_1x + ... + a_nx^n
vector<ll> pol[N];

//True if n is prime, false otherwise
bool prime[M];

//Sieve for primes. Can be shown to have runtime O(M * log log M)
void sieve() {
	for(int i = 2; i < M; ++i) {
		if(prime[i]) {
			prime[i] = false;
			continue;
		}
		for(int j = i; j < M; j+=i) {
			prime[j] = true;
		}
	}
}


//Input: integers a, b, such that gcd(a, b) = 1
//Return: such integers x, y that ax + by = 1


pll extEuc(ll a, ll b) {
	if(b == 1) {
		return {1, -(a-1)};
	}
	pll c = extEuc(b, a%b);
	//c.F * b + a%b * c.S = 1
	//a%b = a - kb, where k = a/b
	//c.F * b + (a - kb)*c.S = 
	//a*c.S + (c.F - k*c.S)*b = 1
	pll ret = {c.S, c.F - a/b * c.S};
	if(c.S < 0) {
		ret.F += b;
		ret.S -= a;
	}
	return ret;
}

//Input: integer a, prime p, such that a is not divisible by p
//Output: integer b such that ab = 1 (mod p)
ll inv(ll a, ll p) {
	ll ans = (extEuc(a, p).F)%p;
	if(ans < 0) ans += p;
	return ans;
}

/*
Input: polynomial P, prime p
Output: If x is a root of P, return x^deg(P) in terms of x^i with i < deg(P)
The output vector contains the coefficients of the terms, starting with the constant term
Everything is done modulo p, and the output has the coefficients modulo p
If p divides the leading term's coefficient of P, returns an empty vector
*/

vector<ll> calc(vector<ll> P, ll p) {
	int deg = P.size() - 1;
	vector<ll> ans;
	if(P[deg]%p == 0) {
		//p diides the leading term's coefficient
		return ans;
	}

	if(P[deg] != 1) {
		//Multiply each coefficient of P so that P is monic
		ll inverse = inv(P[P.size() - 1], p);
		for(int i = 0; i < P.size(); ++i) {
			P[i] *= inverse;
			P[i] %= p;
		}
	}
	for(int i = 0; i < deg; ++i) {
		ans.push_back((p - P[i])%p);
	}
	return ans;
}


//Input: vector<ll> a, an integer k, a prime p
//Output: the elements of a multiplied by k, where multiplication is done modulo p 

vector<ll> multi(vector<ll> a, ll k, ll p) {
	vector<ll> ans;
	for(int i = 0; i < a.size(); ++i) {
		ans.push_back((k*a[i])%p);
	}
	return ans;
}


//Input: two vector<ll> a and b, and a prime p. Assumes a.size() == b.size()
//Output: the vector which contains elements of the form a[i] + b[i], where addition is done modulo p
vector<ll> add(vector<ll> a, vector<ll> b, ll p) {
	vector<ll> ans;
	for(int i = 0; i < a.size(); ++i) {
		ans.push_back((a[i] + b[i])%p);
	}
	return ans;
}



//Input: integer n indicating the number of input polynomials, and a prime p
//Output: desired polynomial's D coefficients modulo p, when D is chosen to be monic
//If an error occurs, that is, the solution is not unique, returns an empty vector

vector<ll> extend(int n, ll p) {
	//Calculate the products of input polynomial's degrees
	int prod[N];
	prod[0] = 1;
	for(int i = 1; i <= n; ++i) {
		prod[i] = prod[i-1]*(pol[i].size() - 1);
	}

	int pro = prod[n];

	vector<ll> P[N];

	for(int i = 1; i <= n; ++i) {
		P[i] = calc(pol[i], p);
		if(P[i].size() == 0) {
			//p divides the leading term's coefficient
			vector<ll> ret;
			return ret;
		}
	}
	//Calculate s^0, s^1, ... s^pro. Stores the coefficients of each s^i as a vector
	//Each element is written as a linear combination of the natural basis
	vector<ll> power[pro + 1];

	//The first value
	power[0].push_back(1);
	for(int i = 1; i < pro; ++i) {
		power[0].push_back(0);
	}


	for(int i = 1; i <= pro; ++i) {
		//Calculate s^i. The idea is similar as in the other algorithm.
		for(int j = 0; j < pro; ++j) {

			vector<int> a;
			for(int k = 1; k <= n; ++k) {
				a.push_back((j%prod[k])/prod[k-1]);
			}
			ll res = 0;
			for(int k = 1; k <= n; ++k) {
				if(a[k-1] != 0) { 
					int newJ = j - prod[k-1];
					res += power[i-1][newJ];
					if(res >= p) res -= p;
				}
				int newJ = j - ((j%prod[k])/prod[k-1])*prod[k-1];
				newJ += prod[k-1] * (prod[k]/prod[k-1] - 1);
				res += (power[i-1][newJ]*P[k][a[k-1]])%p;
				if(res >= p) res -= p;
			}
			power[i].push_back(res);
		}
	}


	//Matrix corresponding to the solution to the system. 
	//Each element of the array contains one row
	vector<ll> row[pro];

	for(int j = 0; j < pro; ++j) {
		for(int i = 0; i <= pro; ++i) {
			row[j].push_back(power[i][j]);
		}
	}


	//Solve the system by Gaussian-Jordan
	int r = 0;
	for(int col = 0; col < pro; ++col) {
		int ind = r;
		while(row[ind][col] == 0) {
			++ind;
			if(ind == pro) {
				break;
			}
		}
		if(ind == pro) {
			continue;
		} 
		if(ind != r) {
			swap(row[ind], row[r]);
		}
		row[r] = multi(row[r], inv(row[r][col], p), p);
		for(int j = 0; j < pro; ++j) {
			if(j == r) continue;
			row[j] = add(row[j], multi(row[r], p-row[j][col], p), p);
		}
		++r;
	}

	//Determine if the solution is unique, given that D is monic.
	bool uniqueSolution = true;
	vector<ll> ind[pro];

	for(int ro = 0; ro < pro; ++ro) {
		int counter = 0;
		for(int j = 0; j <= pro; ++j) {
			if(row[ro][j] != 0) {
				ind[ro].push_back(j);
			}
		}
		if(ind[ro].size() == 0) {
			uniqueSolution = false;
			break;
		}
	}

	if(!uniqueSolution) {
		//Solution is not unique
		vector<ll> ret;
		return ret;
	}

	//Calculate and return the answer
	int ans[pro];
	for(int i = 0; i < pro; ++i) {
		ans[i] = 0;
	}

	for(int col = 0; col < pro; ++col) {
		for(int ro = 0; ro < pro; ++ro) {
			int k = row[ro][col];
			if(k == 0) continue;
			
			if(ind[ro][ind[ro].size() - 1] == pro) {
				int a = row[ro][pro];
				ans[col] = p - a;
			} else {
				ans[col] = 0;
			}
		}
	}

	vector<ll> an;
	for(int j = 0; j < pro; ++j) {
		an.push_back(ans[j]);
	}
	an.push_back(1);


	return an;

}


int main() {

	/*
	Reading the input
	On the first line of the input there should be an integer n, the amount of polynomials
	On each of the following n lines there should be:
	an integer d, corresponding to the degree of the next polynomial
	and d + 1 integers, the i:th one corresponding to the coefficient of x^{d - i + 1}
	
	Example: for two polynomials x^2 + 1 and x^2 - 2 the input would be
	2
	2 1 0 1
	2 1 0 -2


	*/
	int n;
	cin >> n;

	//lo contains the logarithm of the target bound
	double lo = n;
	ll prod = 1;

	for(int i = 1; i <= n; ++i) {
		int d;
		cin >> d;
		prod *= d;
		ll ma = 0;
		for(int j = d; j >= 0; --j) {
			ll a;
			cin >> a;
			pol[i].push_back(a);
			ma = max(ma, abs(a));
		}
		lo += ma;
		//The algorithm assumes polynomials are given constant term first
		//Humans are more used to giving the highest power term first
		reverse(pol[i].begin(), pol[i].end());
	}

	lo = log(lo);
	lo *= prod;

	//Sieve for the primes
	sieve();


	
	//cur contains the logarithm of the products of working primes calculated so far
	double cur = 0;

	//changes contains information on whether the answer still changes or not
	bool changes = true;

	//We will store the answer to the polynomial D
	vector<lll> D;

	//Modulo for Chinese Remainder Theorem. Product of working primes so far
	lll mo = 1;
	int maxP = -1;
	int am = 0;

	for(int p = C; cur < lo + 1 || changes; ++p) {
		//Only checks large primes - we could pick even larger primes, but
		//not much bigger than 10^9 because of overflow with multiplication
		//(long long has a maximum value of about 10^18)

		if(p == M) {
			/*
			We have not found enough primes to determine the answer
			In theory this could just be bad luck, but in practice the amount
			of primes needed for the calculations is much less than the amount
			we can use. For example, with the test input written above, the
			maximum prime used is just 501947 with C = 5e5, while we can check
			for primes up to M = 6e5. 
			*/
			cout << "The input given does not satisfy the assumptions made!\n";
			return 0;
		}

		if(prime[p] == false) {
			//We do not handle composite numbers
			continue;
		}
		++am;
		//The coefficients of D modulo p
		vector<ll> Dp = extend(n, p);
		if(Dp.size() == 0) {
			//p is not a working prime
			continue;
		}
		maxP = p;
		cur += log(p);

		if(D.size() == 0) {
			//p is the first prime that works
			for(int i = 0; i < Dp.size(); ++i) {
				D.push_back((int) Dp[i]);
			}
			mo = p;
			continue;
		}

		//Update the coefficients of D given the new information of the coefficients
		lll k = (mo%p);
		int t = (int) k.get_si();
		changes = false;
		for(int i = 0; i <= prod; ++i) {
			lll a = D[i];
			lll b = (int) Dp[i];

			int o = inv(t, p);
			lll x = o;
			x *= b-a;
			x *= mo;
			x += a;
			x %= mo*p;
			if(x < 0) x += mo*p;
			D[i] = x;

			//Check for changes
			if(a > mo/2) {
				a -= mo;
			}
			lll resA = a%p; if(resA < 0) resA+=p;
			if(resA != b%p) {
				changes = true;
			}

		}
		mo *= p;

	}
	cout << "The maximum prime: " << maxP << "\n";
	cout << "Amount: " << am << "\n";

	//Check the signs of the coefficients
	for(int i = 0; i < D.size(); ++i) {
		lll k = D[i];
		k %= mo;
		if(k > mo/2) {
			k -= mo;
		}
		D[i] = k;
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
		reverse(pol[i].begin(), pol[i].end());
		cout << pol[i].size() - 1 << "\n";
		for(int j = 0; j < pol[i].size(); ++j) {
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