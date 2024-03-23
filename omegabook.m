(* ::Package:: *)

(* Mathematica Package *)
BeginPackage["omegabook`"]

x::usage = "x[...] are spacetime coordinates along topological directions.";
z::usage = "z[...] are spacetime coordinates along holomorphic directions.";
\[Delta]::usage = "\[Delta][...] are holomorphic shift along spacetime coordinates along holomorphic directions.";
zb::usage = "zb[...] are spacetime coordinates along anti-holomorphic directions.";
ze::usage = "z[...] are spacetime coordinates along holomorphic directions associated to an edge";
t::usage = "t[...] are Schwinger times.";
\[Lambda]::usage = "\[Lambda][...] are lambda parameter, or holomorphic momenta.";
wedge::usage = "wedge[...] computes the wedge product of the input forms.";
dif::usage = "dif[...] represents a differential form.";
smeasure::usage = "smeasure[g_Graph] computes the smeasure for the graph g.";
con::usage = "con[...] is a condition function used within the package.";
orderdif::usage = "orderdif[exp] orders differential expressions.";
xvars::usage = "xvars[g_Graph] returns the x variables associated with the graph g.";
dxvars::usage = "dxvars[g_Graph] returns the differential x variables of the graph g.";
tvars::usage = "tvars[g_Graph] returns the t variables associated with the graph g.";
dtvars::usage = "dtvars[g_Graph] returns the differential t variables of the graph g.";
svars::usage = "svars[g_Graph] calculates s variables for the graph g.";
dsvars::usage = "dsvars[g_Graph] calculates differential s variables for the graph g.";
stmeasure::usage = "stmeasure[g_Graph] calculates the st measure for the graph g.";
sexp::usage = "sexp[g_Graph] calculates the s expression for the graph g.";
sA::usage = "sA[g_Graph] calculates the action sA for the graph g.";
isA::usage = "isA[g_Graph] calculates the inverse of the action sA for the graph g.";
swick::usage = "swick[g_Graph][a] applies the Wick's theorem.";
somega::usage = "somega[g_Graph] calculates the omega function for the graph g.";
sAfromAM::usage = "sAfromAM[g_Graph] derives sA from the adjacency matrix of the graph.";
zvars::usage = "zvars[g_Graph] returns the z variables associated with the graph g.";
zevars::usage = "zevars[g_Graph] returns the ze variables of the graph g.";
zbvars::usage = "zbvars[g_Graph] returns the zb variables associated with the graph g.";
\[Lambda]vars::usage = "\[Lambda]vars[g_Graph] returns the lambda variables of the graph g.";
dzbvars::usage = "dzbvars[g_Graph] returns the differential zb variables of the graph g.";
\[Delta]vars::usage = "\[Delta]vars[g_Graph] returns the delta variables of the graph g.";
yvars::usage = "yvars[g_Graph] calculates y variables for the graph g.";
dyvars::usage = "dyvars[g_Graph] calculates differential y variables for the graph g.";
ymeasure::usage = "ymeasure[g_Graph] calculates the y measure for the graph g.";
ytmeasure::usage = "ytmeasure[g_Graph] calculates the yt measure for the graph g.";
x\[Delta]B::usage = "x\[Delta]B[g_Graph] calculates x\[Delta]B for the graph g.";
xyexp::usage = "xyexp[g_Graph] calculates the xy expression for the graph g.";
xyA::usage = "xyA[g_Graph] calculates the xy action for the graph g.";
ixyA::usage = "ixyA[g_Graph] calculates the inverse of the xy action for the graph g.";
xywick::usage = "xywick[g_Graph][a] applies the Wick's theorem in the xy context.";
xyomega::usage = "xyomega[g_Graph] calculates the omega function for the xy context.";
print::usage = "print[g_Graph] prints the graph g with vertex labels.";
changeEdgeLabel::usage = "changeEdgeLabel[graph1] changes the labels of the edges in the graph.";
Adefect::usage = "Adefect[exp, xvarslist] calculates the A defect for the given expression and variables list.";
wickdefect::usage = "wickdefect[exp, xvarslist][a] applies Wick's theorem with a defect.";
wickCustomAHol::usage = "wickCustomAHol[A, zvarslist, zbvarslist][a] applies a custom Wick's theorem in a holomorphic context.";
dtttt::usage = "dtttt[list] performs a differential operation on the list.";
printBeauty::usage = "printBeauty[exp]";
lamanSubgraphTestQ::usage = "lamanSubgraphTestQ";
lamanQ::usage = "lamanQ";
lamanQall::usage = "check Laman condition for all values of HT";


Begin["`Private`"]
(* Initialization of the Wedge Product Functionality *)

(* Default wedge product value when no arguments are passed. *)
wedge[] := 1;

(* Distributive property over addition. *)
wedge[a___, b_ + c_, d___] := wedge[a, b, d] + wedge[a, c, d];

(* In such cases, the non-differential term is factored out. *)
wedge[a___, b_, c___] := b wedge[a, c] /; FreeQ[b, dif];

(* The scalar is factored out according to the properties of the wedge product. *)
wedge[a___, b_*c_, d___] := b wedge[a, c, d] /; FreeQ[b, dif];

(* Base case for the differential form 'dif'. *)
dif[] := 1;

(* Differential form of 0 is defined to be 0, representing an empty differential form. *)
dif[a___, 0, b___] := 0;

(* Application of the wedge product to differential forms, ensuring antisymmetry and sorting. *)
wedge[a___, dif[b___], dif[c___], d___] := 
 If[DuplicateFreeQ[Join[{b}, {c}]], 
  Signature[Join[{b}, {c}]] wedge[a, dif @@ Sort[Join[{b}, {c}]], d],
  0];

(* Simplification rule for wedge products involving a single differential form. *)
wedge[dif[a___]] := dif[a];

(* 'con' function for applying contractions to differential forms. *)
con[a___] := (dif[b___] :> If[SubsetQ[{b}, {a}], Signature[Join[{a}, Complement[{b}, {a}]]] dif @@ Complement[{b}, {a}], 0]);

(* 'orderdif' function to sort differential forms according to their arguments. *)
orderdif[exp_] := exp /. {dif[arg__] :> Signature[{arg}] dif @@ Sort[{arg}]};


(* x: coordinate along topological direction*)
(* t: Schwinger time*)
(* s = x/Sqrt[t] *)
(* Topological forms *)
(*xvars[g_Graph]:=Table[x[i],{i,1,VertexCount[g]}]*)
xvars[g_Graph]:=Table[x[i],{i,VertexList[g]}];
dxvars[g_Graph]:=Thread[dif[xvars[g]]];

(*tvars[g_Graph]:=Table[t[i],{i,1,EdgeCount[g]}]*)
tvars[g_Graph]:=Table[t[i],{i,EdgeList[g]}];
dtvars[g_Graph]:=Thread[dif[tvars[g]]];

svars[g_Graph]:=DiagonalMatrix[tvars[g]^(-1/2)] . Transpose[IncidenceMatrix[g]] . xvars[g];
dsvars[g_Graph]:=DiagonalMatrix[-1/2 tvars[g]^(-3/2)] . DiagonalMatrix[dtvars[g]] . Transpose[IncidenceMatrix[g]] . xvars[g]+DiagonalMatrix[tvars[g]^(-1/2)] . Transpose[IncidenceMatrix[g]] . dxvars[g];
(*IncidenceMatrix = Subscript[I, ve]*)

(*smeasure[g_Graph]:=wedge@@dsvars[g]/.x[VertexCount[g]]->0*)(* \[CapitalPi] ds over all edges *)
smeasure[g_Graph]:=wedge@@dsvars[g]/.x[VertexList[g][[-1]]]->0;
(*here s is only one of T topological directions*)(*put the last xv to the origin*)
stmeasure[g_Graph]:=smeasure[g]/.(con@@Drop[xvars[g],-1]);(*remove Subscript[dx, v] part and only left with dt part*)

smeasure[g_Graph,v_]:=wedge@@dsvars[g]/.x[v]->0;(* \[CapitalPi] ds over all edges *)(*here s is only one of T topological directions*)(*put the last xv to the origin*)
stmeasure[g_Graph,v_]:=smeasure[g,v]/.(con@@DeleteCases[xvars[g],x[v]]);(*remove Subscript[dx, v] part and only left with dt part*)

sexp[g_Graph]:=svars[g] . svars[g];
sA[g_Graph]:=Table[D[D[sexp[g],i],j],{i,Drop[xvars[g],-1]},{j,Drop[xvars[g],-1]}];(*exp(-S), S =1/2Subscript[x, i] A^ij Subscript[x, j]*)
isA[g_Graph]:=Inverse[sA[g]];(* A^-1 *)
swick[g_Graph][a_]:=Tr[isA[g] . Table[1/2D[D[a,i],j],{i,Drop[xvars[g],-1]},{j,Drop[xvars[g],-1]}]];
somega[g_Graph]:=Sqrt[(2\[Pi])^Length[sA[g]]/Det[sA[g]]]If[
EvenQ[(EdgeCount[g]-VertexCount[g]+1)],
Nest[swick[g],stmeasure[g],(EdgeCount[g]-VertexCount[g]+1)/2](*true for general H+T !*)
,0];

sAfromAM[g_Graph]:=(DiagonalMatrix[Table[Total[1/(t/@(Union[EdgeList[g,v\[DirectedEdge]_],EdgeList[g,_\[DirectedEdge]v]]))],{v,VertexList[g]}]]-WeightedAdjacencyMatrix[g,EdgeWeight->(1/(t/@EdgeList[g]))]-Transpose[WeightedAdjacencyMatrix[g,EdgeWeight->(1/(t/@EdgeList[g]))]]//Normal)[[;;-2,;;-2]];
(*build the action sA from the Adjacent Matrix*)


(* z, zb: coordinate along holomorphic direction*)
(* t: Schwinger time*)
(* y = zb/t *)
(* Topological forms *)
zvars[g_Graph]:=Table[z[i],{i,VertexList[g]}]
zevars[g_Graph]:=Table[ze[i],{i,EdgeList[g]}]
zbvars[g_Graph]:=Table[zb[i],{i,VertexList[g]}]
\[Lambda]vars[g_Graph]:=Table[\[Lambda][i],{i,VertexList[g]}]

dzbvars[g_Graph]:=Thread[dif[zbvars[g]]]
\[Delta]vars[g_Graph]:=Table[\[Delta][i],{i,EdgeList[g]}] (*define the shift for each edge*)

(*tvars[g_Graph]:=Table[t[i],{i,EdgeList[g]}]
dtvars[g_Graph]:=Thread[dif[tvars[g]]]*)(* has been difined above in top section already*)

yvars[g_Graph]:=DiagonalMatrix[tvars[g]^(-1)] . Transpose[IncidenceMatrix[g]] . zbvars[g]   (*define y for each edge*)

dyvars[g_Graph]:=DiagonalMatrix[- tvars[g]^(-2)] . DiagonalMatrix[dtvars[g]] . Transpose[IncidenceMatrix[g]] . zbvars[g]+DiagonalMatrix[tvars[g]^(-1)] . Transpose[IncidenceMatrix[g]] . dzbvars[g]
(*IncidenceMatrix = Subscript[I, ve]*)

ymeasure[g_Graph]:=(Exp[zvars[g] . \[Lambda]vars[g]])wedge@@dyvars[g]/.{zb[VertexList[g][[-1]]]->0,z[VertexList[g][[-1]]]->0}(* \[CapitalPi] dy over all edges *)(*here y is only one of H holomorphic directions*)(*put the last xv to the origin*)
ytmeasure[g_Graph]:=ymeasure[g]/.(con@@Drop[zbvars[g],-1])(*remove Subscript[dx, v] part and only left with dt part*)

ymeasure[g_Graph,v_]:=wedge@@dyvars[g]/.{zb[v]->0,z[v]->0}(* \[CapitalPi] dy over all edges *)(*put the some chosen xv to the origin*)
ytmeasure[g_Graph,v_]:=ymeasure[g,v]/.(con@@DeleteCases[zbvars[g],zb[v]])(*remove Subscript[dx, v] part and only left with dt part*)

x\[Delta]B[g_Graph]:=Table[D[D[xyexp[g],i],j],{i,Drop[zbvars[g],-1]},{j,\[Delta]vars[g]}]

xyexp[g_Graph]:=(zvars[g]) . IncidenceMatrix[g] . yvars[g]+\[Delta]vars[g] . yvars[g]
xyA[g_Graph]:=Table[D[D[xyexp[g],i],j],{i,Drop[zvars[g],-1]},{j,Drop[zbvars[g],-1]}](*S = Subscript[z, i] A^ij Subscript[zb, j]*)
ixyA[g_Graph]:=Inverse[xyA[g]]       (* A^-1 *)

xywick[g_Graph][a_]:=Tr[ixyA[g] . Table[D[D[a,i],j],{i,Drop[zvars[g],-1]},{j,Drop[zbvars[g],-1]}]];
xyomega[g_Graph]:=
Sqrt[(((2\[Pi])^(2Length[xyA[g]]))/(4^Length[xyA[g]] Det[xyA[g]]^2))](Nest[xywick[g],ytmeasure[g],(EdgeCount[g]-VertexCount[g]+1)]);


print[g_Graph]:=Graph[g,VertexLabels->Table[i->ToString[i],{i,VertexList[g]}],ImageSize->70]

changeEdgeLabel[graph1_] := Flatten[
{Table[t[i]->t[EdgeList[graph1][[i]]],{i,EdgeCount[graph1]}],Table[\[Delta][i]->\[Delta][EdgeList[graph1][[i]]],{i,EdgeCount[graph1]}]}]
ClearAll[Adefect,wickdefect]
Adefect[exp_,xvarslist_]:=Table[D[D[exp,i],j],{i,xvarslist},{j,xvarslist}](*S = 1/2 Subscript[x, i] A^ij Subscript[x, j]*)
Adefect[exp_,xvarslist_,zvarslist_,zbvarslist_]:={Table[D[D[exp,i],j],{i,xvarslist},{j,xvarslist}],Table[D[D[exp,i],j],{i,zvarslist},{j,zbvarslist}]}(*S = 1/2 Subscript[x, i] A^ij Subscript[x, j] + z B zb*)
wickdefect[exp_,xvarslist_][a_]:=Tr[Inverse[Adefect[exp,xvarslist]] . Table[1/2D[D[a,i],j],{i,xvarslist},{j,xvarslist}]]
wickdefect[exp_,xvarslist_,zvarslist_,zbvarslist_][a_]:=Tr[Inverse[Adefect[exp,xvarslist,zvarslist,zbvarslist][[1]]] . Table[1/2D[D[a,i],j],{i,xvarslist},{j,xvarslist}]]+Tr[Inverse[Adefect[exp,xvarslist,zvarslist,zbvarslist][[2]]] . Table[D[D[a,i],j],{i,zvarslist},{j,zbvarslist}]]
wickCustomAHol[A_,zvarslist_,zbvarslist_][a_]:=Tr[Inverse[A] . Table[D[D[a,i],j],{i,zvarslist},{j,zbvarslist}]]

dtttt[list_]:=Module[{},
Sum[(-1)^i dif[Drop[list,{i}]/.List->Sequence]/Times@@(Drop[list,{i}]),{i,Length[list]}]
]
$Assumptions=Element[{t[12],t[13],t[14],t[23],t[34],Subscript[t, 12], Subscript[t, 23], Subscript[t, 24], Subscript[t, 31], Subscript[t, 43]},PositiveReals];
printBeauty[exp_]:=(exp/.{t[i_\[DirectedEdge]j_]:>t[10i+j],ze[i_\[DirectedEdge]j_]:>ze[10i+j]}/.{t[a_]:>Subscript[t,a] ,ze[a_]:>Subscript[ze,a] })//FullSimplify(*//FullSimplify[#, t[12]>0&& t[13]>0&& t[14]>0&&t[23]>0&&t[34]>0&&Subscript[t,a_]>0]&*)


(* Laman graph tests *)
lamanSubgraphTestQ[g_Graph,HT_]:=(HT-1)EdgeCount[g]<=(HT) VertexCount[g]-(HT+1);
lamanQ[g_Graph,HT_Integer]:=((HT-1)EdgeCount[g]==HT VertexCount[g]-(HT+1))&&(And@@Map[lamanSubgraphTestQ[Subgraph[g,#],HT]&][Subsets[VertexList[g],{2,VertexCount[g]}]])
lamanQall[g_Graph]:=Table[lamanQ[g,HT],{HT,1,6}]


Print["Success! Welcome to Holomorphic Twist"]


End[]
EndPackage[]
