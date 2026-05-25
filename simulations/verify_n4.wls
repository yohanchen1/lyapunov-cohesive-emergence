(* verify_n4.wls *)
(* Numeric verification of dE/dt = Vdot identity for n=4 + statistical testing *)

Print["================================================================"];
Print["  DCNG dE/dt Numeric Verification -- n=4"];
Print["  dE/dt = -Sum phi'(x_i) (x_i - Sum_j w_ij phi_j)^2"];
Print["          - eps Sum_{(i,j)} (alpha w_ij - phi_i phi_j)^2"];
Print["================================================================"];

eps = 0.1; alpha = 0.5;
n = 4;
edges = {{1,2}, {1,3}, {2,3}, {2,4}, {3,4}};
m = Length[edges];

(* ===== Single random configuration ===== *)
Print["\n--- Single configuration test ---"];

SeedRandom[42];
xv = RandomReal[{-2, 2}, n];
wmat = ConstantArray[0, {n, n}];
For[k = 1, k <= m, k++,
  {i, j} = edges[[k]];
  val = RandomReal[{-1, 1}];
  wmat[[i, j]] = val; wmat[[j, i]] = val;
];

phiVec = Tanh[xv];
ppVec = Sech[xv]^2;

AVec = Table[Sum[wmat[[i, j]] * phiVec[[j]], {j, 1, n}], {i, 1, n}];
xdotVec = -xv + AVec;

term1Single = -Sum[ppVec[[i]] * xdotVec[[i]]^2, {i, 1, n}];
term2Single = -eps * Sum[
  (alpha * wmat[[edges[[k,1]], edges[[k,2]]]] - phiVec[[edges[[k,1]]]] * phiVec[[edges[[k,2]]]])^2,
  {k, 1, m}
];
dEdtSingle = term1Single + term2Single;

Print["x           = ", xv];
Print["phi(x)      = ", phiVec];
Print["Term1       = ", term1Single];
Print["Term2       = ", term2Single];
Print["dE/dt       = ", dEdtSingle];
Print["dE/dt <= 0? = ", dEdtSingle <= 0];

(* ===== Statistical: 1000 random configs ===== *)
Print["\n--- Statistical test: 1000 random configs ---"];

nTests = 1000;
nPass = 0;
maxVal = -10^9;
minVal = 10^9;

For[t = 1, t <= nTests, t++,
  xt = RandomReal[{-3, 3}, n];
  wt = ConstantArray[0, {n, n}];
  For[k = 1, k <= m, k++,
    {i, j} = edges[[k]];
    val = RandomReal[{-2, 2}];
    wt[[i, j]] = val; wt[[j, i]] = val;
  ];
  pht = Tanh[xt];
  ppt = Sech[xt]^2;
  At = Table[Sum[wt[[i, j]] * pht[[j]], {j, 1, n}], {i, 1, n}];
  xdt = -xt + At;
  v1 = -Sum[ppt[[i]] * xdt[[i]]^2, {i, 1, n}];
  v2 = -eps * Sum[
    (alpha * wt[[edges[[k,1]], edges[[k,2]]]] - pht[[edges[[k,1]]]] * pht[[edges[[k,2]]]])^2,
    {k, 1, m}
  ];
  vt = v1 + v2;
  If[vt <= 0, nPass++];
  If[vt > maxVal, maxVal = vt];
  If[vt < minVal, minVal = vt];
];

Print["Configs:    ", nTests];
Print["dE/dt <= 0: ", nPass, " / ", nTests];
Print["Max dE/dt:  ", maxVal];
Print["Min dE/dt:  ", minVal];

If[nPass == nTests,
  Print["*** n=4 ALL PASS: dE/dt <= 0 for all configurations ***"],
  Print["*** n=4 WARNING: ", nTests - nPass, " violations ***"]
];

Print["================================================================"];
