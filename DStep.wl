(* ::Package:: *)

BeginPackage["DStep`"]


Begin["`Private`"]


baseRules={
  d[c_,x_]/;FreeQ[c,x]:>0,
  d[lf_Plus,x_]:>Thread[d[lf,x],Plus],
  d[c_*f_,x_]/;FreeQ[c,x]:>c*d[f,x],
  d[f_*g_,x_]:>d[f,x]g+d[g,x]f
};

higherRules={
  HoldPattern@d[InverseFunction[f_][x_],x_]:>1/dfunc[f,InverseFunction[f][x]],
  d[f_[g_],x_]/;g=!=x:>dfunc[f,g]d[g,x],
  d[f_[g_,c_],x_]/;FreeQ[c,x]&&g=!=x:>dfunc[f[#,c]&,g]d[g,x],
  d[f_[c_,g_],x_]/;FreeQ[c,x]&&g=!=x:>dfunc[f[c,#]&,g]d[g,x]
};

substRules=dfunc[f_,g_]:>Module[{u},
  With[{df=dEval[f[u],u]},
    (df/.{u->g})/;FreeQ[df,_d|_dfunc]
  ]
];

functionRules=Table[
  With[{f=f},HoldPattern@d[IgnoringInactive@f[x_],x_]]->D[f[x],x],
  {f,{
    Sqrt,CubeRoot,RealAbs,
    Exp,Log,Log2,Log10,
    Sin,Cos,Tan,Cot,Sec,Csc,
    ArcSin,ArcCos,ArcTan,ArcCot,ArcSec,ArcCsc,
    Sinh,Cosh,Tanh,Coth,Sech,Csch,
    ArcSinh,ArcCosh,ArcTanh,ArcCoth,ArcSech,ArcCsch
    }
  }
]/.{Rule->RuleDelayed};
functionExtRules={
  HoldPattern@d[x_^a_.,x_]/;FreeQ[a,x]:>a x^(a-1),
  HoldPattern@d[a_^x_,x_]/;FreeQ[a,x]:>a^x Log[a],
  HoldPattern@d[IgnoringInactive@Surd[x_,n_],x_]/;FreeQ[n,x]:>1/(n Surd[x,n]^(n-1))
};

transferRules={
  HoldPattern@d[IgnoringInactive[f_^g_],x_]/;!(FreeQ[f,x]||FreeQ[g,x]):>d[Inactive[Exp][Log[f]g],x],
  HoldPattern@d[IgnoringInactive@Log[f_,g_],x_]:>d[Log[g]/Log[f],x]
};


$dDepth=0;

echoStep0[expr_]:=(
  CellPrint@Cell[BoxData[FormBox[ToBoxes[expr,TraditionalForm],TraditionalForm]],"Print",
    CellMargins->{{Inherited+20($dDepth-1), Inherited},{Inherited,Inherited}}];
  expr
)

echoStep[expr_]:=(
  CellPrint@Cell[BoxData[FormBox[ToBoxes[expr,TraditionalForm],TraditionalForm]],"Print",
    CellDingbat->Cell["=","EchoLabel"],
    CellMargins->{{Inherited+20$dDepth, Inherited},{Inherited,Inherited}}];
  expr
)


dEval[f_,x_]:=Block[{$dDepth=$dDepth+1},dEvalR[f,x]]
dEvalR[f_,x_]:=NestWhile[echoStep@*ReplaceAll[allRules],echoStep0[d[f,x]],!FreeQ[#2,_d|_dfunc]&&UnsameQ[##]&,2]
stepD[f_,x_]:=With[{eval=dEval[f,x]},eval/;FreeQ[eval,_d|_dfunc]]


End[]


EndPackage[]
