# incomplete_gamma_int
 
The Maxima CAS package `incomplete_gamma_int` attempts to find a change of variable 
that converts a given integrand to the form $\int \mathrm{e}^{-t} t^a \mathrm{d}t$. 
When successful, Maxima returns the antiderivative in terms of the incomplete gamma 
function. A simple example is:
 ~~~~
(%i1)	incomplete_gamma_int(sqrt(x-1)*sqrt(x)*(2*x-1)*%e^(x-x^2),x);
(%o1)	-gamma_incomplete(3/2,(x-1)*x)
 ~~~~
