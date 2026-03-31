# Cohomology of moduli spaces of curves.

We list computational results for [this paper](https://arxiv.org/abs/2603.26962).

We calculate the Sn-equivariant Hodge-Serre polynomial of moduli spaces of n-pointed genus g smooth curves Mgn, curves with rational tail Mrtgn, and curves of compact type Mctgn. 

These results were computed using Deligne's weight spectral sequence.
Of particular note are the two new results for smooth curves: M50 and M33.
For these two spaces we used the pullback spectral sequence to calculate the weights <= 4 and the pushforward spectral sequence for the rest.

The Sn-equivariant Hodge-Serre polynomial encodes the dimensions of the weight graded pieces of the (compactly supported) cohomology groups (either $\ell$-adic \'etale cohomology or of rational Hodge structures) together with their action of the symmetric group Sn. More precisely it will consist of monomials of the form d\*t^k\*L^n\*s\[lambda\], where d is the dimension of the lambda-isotypical weight 2*n graded piece of the degree k (compactly supported) cohomology group. Moreover, all weight graded pieces appearing in the tables will be of Tate type.

Note that there is redundacy in the results for rational tail. Since when n < 2, any stable curve with a rational tail is in fact a smooth curve.

The zip file contains the code together with a short readme for instructions. This includes an old version of admcycles.
I plan to integerate the code into admcycles in the near future.
