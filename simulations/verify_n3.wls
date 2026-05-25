(* DCNG Theorem 1 verification - n=3 path graph *)
(* Lean version: symbolic derivatives, numeric eval, no expensive inequality *)

phi[s_] := Tanh[s];
G[x_] := x*Tanh[x] + Log[Sech[x]];

Clear[x1, x2, x3, w12, w23];
alpha = 1; epsilon = 1/10;

(* Dynamics *)
dx1 = -x1 + w12*phi[x2];
dx2 = -x2 + w12*phi[x1] + w23*phi[x3];
dx3 = -x3 + w23*phi[x2];
dw12 = epsilon*(phi[x1]*phi[x2] - alpha*w12);
dw23 = epsilon*(phi[x2]*phi[x3] - alpha*w23);

(* Energy *)
Eterms = -w12*phi[x1]*phi[x2] - w23*phi[x2]*phi[x3] + G[x1] + G[x2] + G[x3] + (alpha/2)*(w12^2 + w23^2);

(* dE/dt by chain rule *)
dEdtSym = D[Eterms, x1]*dx1 + D[Eterms, x2]*dx2 + D[Eterms, x3]*dx3 + D[Eterms, w12]*dw12 + D[Eterms, w23]*dw23;

(* Vdot from Theorem 1 *)
VdotSym = -((1-phi[x1]^2)*dx1^2 + (1-phi[x2]^2)*dx2^2 + (1-phi[x3]^2)*dx3^2) - epsilon*((alpha*w12 - phi[x1]*phi[x2])^2 + (alpha*w23 - phi[x2]*phi[x3])^2);

(* Verify identity symbolically *)
diffSym = Simplify[dEdtSym - VdotSym];

(* Numeric evaluation *)
numRules = {x1 -> 0.5, x2 -> -0.3, x3 -> 0.8, w12 -> 0.4, w23 -> -0.2};
dEdtNum = N[dEdtSym /. numRules];
VdotNum = N[VdotSym /. numRules];

Print["=== Theorem 1 Verification (n=3 path graph) ==="];
Print["dE/dt - Vdot (symbolic)   = ", diffSym];
Print[""];
Print["dE/dt (numeric)          = ", dEdtNum];
Print["Vdot (numeric)           = ", VdotNum];
Print["Difference (numeric)     = ", dEdtNum - VdotNum];
Print["Vdot <= 0?               = ", VdotNum <= 0];
