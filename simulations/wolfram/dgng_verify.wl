(**
 * DGNG 定理 1-3 数值仿真验证
 * 稀疏动态网络中稳定内聚结构的涌现
 * Wolfram Language
 *)

(* === 激活函数 === *)
phi[x_] := Tanh[x]
phiPrime[x_] := Sech[x]^2
Gphi[x_] := x*phi[x] - Log[Cosh[x]]  (* G(φ(x)) ≥ 0 *)

(* === Lyapunov 函数 E 及其导数 === *)
Etotal[x_, W_, n_, alpha_] :=
  -1.0*Sum[If[i<j,W[[i,j]]*phi[x[[i]]]*phi[x[[j]]],0],{i,n},{j,n}] +
  Sum[Gphi[x[[i]]],{i,n}] +
  0.5*alpha*Sum[If[i<j,W[[i,j]]^2,0],{i,n},{j,n}]

dEdtAnalytic[x_, W_, n_, alpha_, eps_] := Module[{A},
  A = Table[Sum[W[[i,j]]*phi[x[[j]]],{j,n}],{i,n}];
  -Sum[phiPrime[x[[i]]]*(x[[i]]-A[[i]])^2,{i,n}] -
  eps*Sum[If[i<j,(alpha*W[[i,j]]-phi[x[[i]]]*phi[x[[j]]])^2,0],{i,n},{j,n}]
]

(* === ODE 动力学 === *)
makeDynamics[adj_, n_, alpha_, eps_] := Function[{t,state},
  Module[{x,W,dx,dW},
    x = state[[1;;n]];
    W = Partition[state[[n+1;;-1]],n];
    dx = Table[-x[[i]]+Sum[W[[i,j]]*phi[x[[j]]],{j,n}],{i,n}];
    dW = Table[If[adj[[i,j]]!=0,eps*(phi[x[[i]]]*phi[x[[j]]]-alpha*W[[i,j]]),0],{i,n},{j,n}];
    Flatten[{dx,Flatten[dW]}]
  ]
]

(* === 生成稀疏图 === *)
sparseGraph[n_, p_] := Module[{adj},
  adj = Table[If[i<j&&RandomReal[]<p,1,0],{i,n},{j,n}];
  adj + Transpose[adj]
]

(* === 运行仿真 === *)
simulate[adj_, alpha_, eps_, tMax_] := Module[{n=Length[adj],x0,W0,state0,dyn},
  SeedRandom[42];
  x0 = RandomReal[{-1,1},n];
  W0 = Table[If[adj[[i,j]]!=0,RandomReal[{-0.3,0.3}],0],{i,n},{j,n}];
  W0 = 0.5*(W0+Transpose[W0]);
  state0 = Flatten[{x0,Flatten[W0]}];
  dyn = makeDynamics[adj,n,alpha,eps];
  NDSolveValue[
    {Table[Indexed[y,{i}]'[t]==dyn[t,Table[Indexed[y,{j}][t],{j,n+n^2}]][[i]],{i,n+n^2}],
     Table[Indexed[y,{i}][0]==state0[[i]],{i,n+n^2}]},
    Table[Indexed[y,{i}],{i,n+n^2}],
    {t,0,tMax}, Method->"StiffnessSwitching",MaxSteps->100000
  ]
]

getState[sol_, n_, t_] := {
  Table[sol[[i]][t],{i,n}],
  Partition[Table[sol[[i]][t],{i,n+1,n+n^2}],n]
}

(* === 符号链式法则验证 dE/dt 解析公式 === *)
(* 对 n=3 全连接图做符号计算，验证链式法则导数与解析公式一致 *)
Module[{nSym=3, symX, symW, aSym, eSym, xdotSym, wdotSym, EtotSym, dEdtChainSym, dEdtAnalyticSym, diff},
  symX = Table[Subscript[x,i], {i, nSym}];
  symW = Table[Subscript[w,i,j], {i, nSym}, {j, nSym}];
  Do[symW[[j,i]] = symW[[i,j]], {i, nSym}, {j, i+1, nSym}];
  aSym = Symbol["alpha"]; eSym = Symbol["eps"];
  EtotSym = -1.0*Sum[If[i<j, symW[[i,j]]*phi[symX[[i]]]*phi[symX[[j]]], 0], {i,nSym},{j,nSym}] +
    Sum[Gphi[symX[[i]]], {i, nSym}] +
    0.5*aSym*Sum[If[i<j, symW[[i,j]]^2,0], {i,nSym},{j,nSym}];
  xdotSym = Table[-symX[[i]]+Sum[symW[[i,j]]*phi[symX[[j]]],{j,nSym}],{i,nSym}];
  wdotSym = Table[If[i<j, eSym*(phi[symX[[i]]]*phi[symX[[j]]]-aSym*symW[[i,j]]),0], {i,nSym},{j,nSym}];
  dEdtChainSym = Sum[D[EtotSym,symX[[i]]]*xdotSym[[i]],{i,nSym}] +
    Sum[If[i<j, D[EtotSym,symW[[i,j]]]*wdotSym[[i,j]],0], {i,nSym},{j,nSym}];
  dEdtAnalyticSym = -Sum[phiPrime[symX[[i]]]*(symX[[i]]-Sum[symW[[i,j]]*phi[symX[[j]]],{j,nSym}])^2,{i,nSym}] -
    eSym*Sum[If[i<j, (aSym*symW[[i,j]]-phi[symX[[i]]]*phi[symX[[j]]])^2,0], {i,nSym},{j,nSym}];
  diff = FullSimplify[dEdtChainSym - dEdtAnalyticSym];
  Print["链式法则验证: dE/dt(chain) - dEdtAnalytic = ", diff];
  If[Expand[dEdtChainSym] === Expand[dEdtAnalyticSym],
    Print["[Verified] 链式法则与解析公式一致 (差=0)"],
    Print["[Warning] 存在差异"]
  ];
];

(* === 验证定理 1: dE/dt ≤ 0 === *)
checkTheorem1[sol_, adj_, n_, alpha_, eps_, tMax_] := Module[{ts,dE},
  ts = Subdivide[0,tMax,200];
  dE = Table[dEdtAnalytic@@Join[getState[sol,n,t],{n,alpha,eps}],{t,ts}];
  Print["定理1: min(dE/dt)=",Min[dE],"  max(dE/dt)=",Max[dE]];
  Min[dE] >= -1.*^-8
]

(* === 验证定理 2: 收敛到平衡点 === *)
checkTheorem2[sol_, adj_, n_, alpha_, eps_, tMax_] := Module[{x,W,dx,dW,tol=1.*^-5},
  {x,W} = getState[sol,n,tMax];
  dx = Max[Abs[Table[-x[[i]]+Sum[W[[i,j]]*phi[x[[j]]],{j,n}],{i,n}]]];
  dW = Max[Abs[Table[If[adj[[i,j]]!=0,
    eps*(phi[x[[i]]]*phi[x[[j]]]-alpha*W[[i,j]]),0],{i,n},{j,n}]]];
  Print["定理2: max|dx|=",dx,"  max|dW|=",dW];
  dx<tol && dW<tol
]

(* === 验证定理 3: δ-内聚划分 === *)
checkTheorem3[sol_, adj_, n_, alpha_, tMax_] := Module[{x,W,pv,vp,vm,vz,ip,im,cw,th,tl,delta},
  {x,W} = getState[sol,n,tMax];
  pv = phi/@x;
  vp = Select[Range[n],pv[[#]]>1.*^-6&];
  vm = Select[Range[n],pv[[#]]<-1.*^-6&];
  vz = Complement[Range[n],vp,vm];
  Print["V+=",Length[vp]," V-=",Length[vm]," V0=",Length[vz]];

  (* Part A: 权重因子化 *)
  Print["PartA 最大残差: ",Max[Table[If[adj[[i,j]]!=0,
    Abs[W[[i,j]]-pv[[i]]*pv[[j]]/alpha],0],{i,n},{j,n}]]];

  If[Length[vp]<1||Length[vm]<1,Print["定理3: 单组退化"];Return[Null]];

  (* 组内/组间权重 *)
  ip = Cases[Flatten[Table[If[adj[[i,j]]!=0&&MemberQ[vp,i]&&MemberQ[vp,j],W[[i,j]],Nothing],{i,n},{j,n}]],_Real];
  im = Cases[Flatten[Table[If[adj[[i,j]]!=0&&MemberQ[vm,i]&&MemberQ[vm,j],W[[i,j]],Nothing],{i,n},{j,n}]],_Real];
  cw = Cases[Flatten[Table[If[adj[[i,j]]!=0&&MemberQ[vp,i]&&MemberQ[vm,j],W[[i,j]],Nothing],{i,n},{j,n}]],_Real];

  Print["V+组内: min=",If[ip!={},Min[ip],"N/A"]," max=",If[ip!={},Max[ip],"N/A"]];
  Print["V-组内: min=",If[im!={},Min[im],"N/A"]," max=",If[im!={},Max[im],"N/A"]];
  Print["组间V+/V-: max=",If[cw!={},Max[cw],"N/A"]," (应<0)"];

  If[ip=={}||im=={}||cw=={},
    Print["缺乏跨组边，无法计算δ"];Return[Null]
  ];
  th = Min[Min[ip],Min[im]]; tl = Max[cw]; delta = th-tl;
  Print["θ_high=",th," θ_low=",tl," δ=",delta," δ/(M^2/α)=",delta/(1/alpha)];

  (* Part D: 自洽方程 *)
  Print["PartD 最大残差: ",Max[Table[If[Abs[pv[[i]]]>1.*^-6,
    Abs[x[[i]]/pv[[i]]-Sum[If[adj[[i,j]]!=0,pv[[j]]^2,0],{j,n}]/alpha],0],{i,n}]]];
  delta>0
]

(* === 完整测试 === *)
test[n_,alpha_,eps_,tMax_,p_:0.3] := Module[{adj,sol,r1,r2,r3},
  adj = sparseGraph[n,p];
  Print["图: n=",n," m=",Total[Flatten[adj]]/2," α=",alpha," ε=",eps];
  sol = simulate[adj,alpha,eps,tMax];
  r1 = checkTheorem1[sol,adj,n,alpha,eps,tMax];
  r2 = checkTheorem2[sol,adj,n,alpha,eps,tMax];
  r3 = checkTheorem3[sol,adj,n,alpha,tMax];
  Print["结果: 定理1=",If[r1,"✅","❌"]," 定理2=",If[r2,"✅","❌"]," 定理3=",If[r3,"✅",If[r3===Null,"⚠️","❌"]]];
  {r1,r2,r3,sol,adj}
]

(* === 绘图 === *)
plotResults[sol_, adj_, n_, alpha_, eps_, tMax_] := Module[{ts,Es},
  ts = Subdivide[0,tMax,500];
  Es = Table[{t,dEdtAnalytic@@Join[getState[sol,n,t],{n,alpha,eps}]},{t,ts}];
  {ListLinePlot[Es,PlotLabel->"dE/dt沿轨迹",AxesLabel->{"t","dE/dt"}],
   ListLinePlot[Table[{t,phi[getState[sol,n,t][[1,i]]]},{i,n},{t,ts}],
     PlotLabel->"φ(x_i) 演化",AxesLabel->{"t","φ(x)"},PlotLegends->Automatic]}
]

(* 运行示例 *)
Print["=== DGNG 定理数值验证 ==="];
result = test[30, 0.5, 0.05, 100.0, 0.3];
