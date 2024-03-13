#import "@local/hrftypst:0.0.1": *
#import "ams_template.typ": *

#show: thmrules
#show: ams-article.with(
  title: "A confusion about the Stern Integral Inequality",
  authors: (
    (
      name: "Henry Ruben Fischer",
    //   department: [Department of Mathematics],
    //   organization: [Georg-August-University Göttingen],
    //   email: "henryruben.fischer@stud.uni-goettingen.de"
    ),
  ),
)

#let theorem = thmbox("theorem", "Theorem", base_level:0)
#let proof = thmplain(
  "proof",
  "Proof",
  bodyfmt: body => [#body #h(1fr) $square$]
).with(numbering: none)
#let definition = thmbox("definition", "Definition")

// #set cite(style:"springer-mathphys")

#let non-harmonic(content) = {
  text(blue)[#content]
}

#let error-terms(content) = {
  text(red)[#content]
}

// copy into hrftypst later
#let laplacian = $Delta$
#let to = $arrow.r$
#let boundary = $diff$
#let disjointunion = $union.sq$
#let partial = $diff$
#let scalarproduct(arg1, arg2,size:auto) = $lr(angle.l arg1, arg2 angle.r,size:size)$
#let Ricci = math.op("Ric")

#let multiline(eq) = {
    assert(type(eq) == content and eq.func() == math.equation)
    if repr(eq.body.func()) != "sequence" { return eq }
    let lines = eq.body.children.split(linebreak()).map(line => {
        block(math.equation(block: true, line.join()))
    })
    if lines.len() <= 1 { return eq }
    
    align(left, lines.first())
    lines.slice(1, -1).map(align.with(center)).join()
    align(right, lines.last())
}

At the end of my Bachelor's thesis about the harmonic level set method for a specific positive mass theorem, I wanted to find out how close the lower bound from the method is to the actual value of the mass, and I did some numerical calculations for a half space version of the Schwarzschild black hole. The convergence of the numerical integral near the critical value of the harmonic function I used was quite terrible, and consequently my values were very rough estimates of the real lower bound, but still this numerical calculation got remarkably close to the actual values of the mass.

Consequently I wanted to understand better what actually prevents the main relevant inequality @brayHarmonicFunctionsMass2019[Proposition 4.2], also referred to as _Stern's inequality_, from being an equality. Below are my calculations where I try to redo the proof of @brayHarmonicFunctionsMass2019[Proposition 4.2] (in some additional generality) while accounting for #error-terms["error terms"] (marked in #error-terms[red]), that were originally just left out (resulting in statements afterwards only being inequalities). On the way we can do a sanity check: The resulting #error-terms[error term] should of course have the same sign everywhere so that we can recover the inequality again.


The following statement is similar to @braySpacetimeHarmonicFunctions2021[Section 4.1], but we allow $abs(nabla u)=0$ at some points. I'm very sure that I must have gotten confused somewhere in the proof, the result seems too strong and would in particular imply that the lower bounds for the mass of @brayHarmonicFunctionsMass2019 and @hirschSpacetimeHarmonicFunctions2021 could be easily strengthened into equalities (just by not replacing the Euler characteristic of the level set $chi(S_t)<=1$ with $1$).

#let maxu = $overline(u)$
#let minu = $underline(u)$
#let nonZeroBoundary = $boundary_(eq.not 0)Omega$

#theorem[
  Let $(Omega,g)$ be a compact 3-dimensional oriented Riemannian manifold with boundary having outward unit normal $nu$. 
  Let $u maps  Omega to  reals$ be any smooth function such that 
  // the set of regular values of $u$ is open and dense (i.e. such that the set of critical values is finite) and such that 
  there exists $C>0$ with $abs(laplacian u) <= C abs(nabla u)$, and denote the open subset of $boundary Omega$ on which $abs(nabla u) != 0$ by $nonZeroBoundary$.
  
  If $maxu$ and $minu$ denote the maximum and minimum of $u$ and $S_t$ are $t$-level sets of $u$, then
  $
    integral_(nonZeroBoundary) (partial_nu abs(nabla u)-laplacian u dot scalarproduct(nu,nabla u)/abs(nabla u)) dif A = &integral_(Omega) 1/2 (abs(nabla^2 u)^2/(abs(nabla u))+R abs(nabla u)- (laplacian u)^2/abs(nabla u) )dif V
    \ &-integral_(minu)^(maxu) (2 pi chi(S_t)-integral_(boundary S_t) kappa_(boundary S_t))dif t
  $
  where $chi(S_t)$ denotes the Euler characteristic of the level sets and $kappa_(boundary S_t)$ denotes the geodesic curvature of $boundary S_t subset S_t$.
]
#proof[
  We follow @hirschSpacetimeHarmonicFunctions2021[Section 3] and @brayHarmonicFunctionsMass2019[Section 4]. We will consider $phi_epsilon colon.eq sqrt(abs(nabla u)+epsilon)$ for $epsilon > 0$ to avoid dealing with $laplacian abs(nabla u)$ at critical values of $u$.

  First, recall Bochner's identity
  $
    1/2 laplacian abs(nabla u)^2=abs(nabla^2 u)^2+Ricci(nabla u, nabla u)+scalarproduct(nabla u, nabla laplacian u),
  $
  which yields in particular
  $
    laplacian phi_epsilon&=(laplacian abs(nabla u)^2)/(2 phi_epsilon)-(abs(nabla abs(nabla u)^2,size:#70%)^2)/(4 phi_epsilon^3)
    \ &=1/(phi_epsilon) (abs(nabla^2 u)^2+Ricci(nabla u, nabla u)-phi_epsilon^(-2) abs(nabla u)^2 abs(nabla abs(nabla u))^2+scalarproduct(nabla u, nabla laplacian u)))
  $
  On regular level sets we have
  $
    laplacian phi_epsilon=1/(2 phi_epsilon)(&abs(nabla^2 u)^2+abs(nabla u)^2 (R_Omega-R_S)+2scalarproduct(nabla laplacian u,nabla u)+(laplacian u)^2 -2laplacian u nabla^2_(nu nu)u
    \ &+2 dot (1-phi_epsilon^(-2)abs(nabla u)^2)abs(nabla abs(nabla u))^2)  
  $

  Note that
  $
    op("div")(laplacian u (nabla u)/phi_epsilon)&=(laplacian u)^2/phi_epsilon+scalarproduct(nabla u, nabla laplacian u)/phi_epsilon-(laplacian u)/phi_epsilon^2 dot nabla_i u nabla^i phi_epsilon
    \ &=(laplacian u)^2/phi_epsilon+scalarproduct(nabla u, nabla laplacian u)/phi_epsilon-(laplacian u)/(2 phi_epsilon^3) dot nabla_i u nabla^i abs(nabla u)^2
    \ &=(laplacian u)^2/phi_epsilon+scalarproduct(nabla u, nabla laplacian u)/phi_epsilon-(laplacian u)/(2 phi_epsilon^3) dot nabla_i u dot 2 dot nabla^i nabla_j u nabla^j u
    \ &=(laplacian u)^2/phi_epsilon+scalarproduct(nabla u, nabla laplacian u)/phi_epsilon-(laplacian u)/(phi_epsilon^3) dot abs(nabla u)^2 dot nabla^2_(nu nu)u
  $

  And thus in general
  $
    op("div")(nabla phi_epsilon-laplacian u (nabla u)/phi_epsilon)=1/(phi_epsilon)(abs(nabla^2 u)^2+Ricci(nabla u, nabla u)-phi_epsilon^(-2)abs(nabla abs(nabla u)^2)^2\/4-(laplacian u)^2+(laplacian u)/(2phi_epsilon^(2))nabla_i u nabla^i abs(nabla u)^2).
  $
  and on regular level sets
  $
      op("div")(nabla phi_epsilon-laplacian u (nabla u)/phi_epsilon)=1/(2 phi_epsilon)(&abs(nabla^2 u)^2+abs(nabla u)^2 (R_Omega-R_S)-(laplacian u)^2
      \ &+2 (1-phi_epsilon^(-2)abs(nabla u)^2)(abs(nabla abs(nabla u))^2-laplacian u nabla^2_(nu nu)u)).
  $
  The additional $2(1-phi_epsilon^(-2)abs(nabla u)^2)(dots.c)$ term vanishes again at the $epsilon->0$ step.

  
  We thus have
  $
    integral_(nonZeroBoundary) (partial_nu abs(nabla u)-laplacian u dot (nabla u)/abs(nabla u)) dif A = integral_(Omega) 1/2 (abs(nabla^2 u)^2/(abs(nabla u))+R abs(nabla u)- (laplacian u)^2/abs(nabla u) dif V)-integral_(minu)^(maxu) 2 pi chi(S_t) dif t
  $
]
#bibliography("ZoteroBibliographyPositiveMassTheoremBachelorThesis.bib")