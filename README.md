## Automated derivative divides for symbolic integration

The Maxima CAS package `incomplete_gamma_int` attempts to find a change of variable that converts 
a given integrand into either the form $\int \mathrm{e}^{-t} t^a  \mathrm{d}t$ or
the form $\int t^a (1-t)^b  \mathrm{d}t$. When successful, the package returns the 
antiderivative in terms of either the incomplete gamma function or the Gauss hypergeometric function. 

The method is akin to an automatic derivative divides (integration by substitution)
with a seed function that involves a so-called special function.

This project started with just the `incomplete_gamma_int` case, and then I extended it.
Likely, I should rename the project.

### Examples

Below are some examples:

```maxima
(%i1) my_int(sqrt(x-1) * sqrt(x) * (2*x-1) * %e^(x-x^2), x);
(%o1) -gamma_incomplete(3/2, (x-1)*x)

(%i2) my_int(x^2*sqrt(1-x^2)^(1/3),x);
(%o2) (hypergeometric([-(1/6),3/2],[5/2],x^2)*x^3)/3

(%i3) my_int(((x-1)*(x+1)*(x^2+1)^(2/3))/x^(8/3),x);
(%o3) (3*(x^2+1)*(x^4+2*x^2+1)^(1/3))/(5*x^(5/3))

(%i4) my_int((x-1)^(2/3)*x^(2/3)*(2*x-1)*sqrt(-x^2+x+1),x);
(%o4) (3*hypergeometric([-(1/2),5/3],[8/3],(x-1)*x)*(x-1)^(5/3)*x^(5/3))/5

(%i5)	my_int((sqrt(-x^2+x-1)*(x^2-1)*(x^2+1)^(1/3))/x^(17/6),x);

(%o5)	(3*hypergeometric([-(1/2),4/3],[7/3],(x^2+1)/x)*(x^2+1)*(x^8-2*x^6+2*x^2-1)^(1/3))/(4*x^(4/3)*(x^6-3*x^4+3*x^2-1)^(1/3))
```

### Mathematica ® Integration Example

Here, we use both plain Mathematica (version 14.1) as well as the [Rubi integrator](https://rulebasedintegration.org/) for example (%o5) from above. Neither gives a satisfactory antiderivative:




```
In[14]:= Integrate[(Sqrt[-x^2 + x - 1] (x^2 - 1) (x^2 + 1)^(1/3))/x^(17/6), x]

Out[14]= ∫(Sqrt[-1 + x - x^2] (-1 + x^2) (1 + x^2)^(1/3))/x^(17/6) dx

In[15]:= Get["Rubi`"]

In[16]:= Int[(Sqrt[-x^2 + x - 1] (x^2 - 1) (x^2 + 1)^(1/3))/x^(17/6), x]

Out[16]= 6 Subst[Int[Sqrt[-1 + x^6 - x^12] (1 + x^12)^(1/3), x], x, x^(1/6)] 
           - 6 Subst[Int[(Sqrt[-1 + x^6 - x^12] (1 + x^12)^(1/3))/x^12, x], x, x^(1/6)]
```
 
### Trademark Attribution

Mathematica is a registered trademark of Wolfram Research, Inc.