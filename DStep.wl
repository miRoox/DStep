(* ::Package:: *)

BeginPackage["DStep`"]


Begin["`Private`"]


d/:MakeBoxes[d[f_,x_],TraditionalForm]:=Module[{boxes},
  boxes=MakeBoxes[f, TraditionalForm];
  If[Precedence[Plus]>=Precedence[boxes,TraditionalForm],boxes=RowBox[{"(", boxes, ")"}]];
  RowBox[{FractionBox["\[DifferentialD]", RowBox[{"\[DifferentialD]", MakeBoxes[x, TraditionalForm]}]], boxes}]
]
dfunc/:MakeBoxes[dfunc[f_, g_], TraditionalForm]:=Module[{fboxes, gboxes},
  fboxes=ToBoxes[f[g], TraditionalForm]; gboxes=ToBoxes[g, TraditionalForm];
  If[Precedence[Plus]>=Precedence[fboxes, TraditionalForm],fboxes=RowBox[{"(", fboxes, ")"}]];
  If[Precedence[Plus]>=Precedence[gboxes, TraditionalForm],gboxes=RowBox[{"(", gboxes, ")"}]];
  FractionBox[RowBox[{"\[DifferentialD]", fboxes}], RowBox[{"\[DifferentialD]", gboxes}]]
]

makeXForm[sym_Symbol]:=sym/:MakeBoxes[sym,TraditionalForm]=ToBoxes[Symbol[StringPart[ToString[sym,InputForm],1]],TraditionalForm]


baseRules={
  d[c_,x_]/;FreeQ[c,x]:>dLabeled[0,"Constant Rule"],
  d[lf_Plus,x_]:>dLabeled[Thread[d[lf,x],Plus],"Linearity Rule"],
  d[c_*f_,x_]/;FreeQ[c,x]:>dLabeled[c*d[f,x],"Linearity Rule"],
  d[f_*g_,x_]:>dLabeled[d[f,x]g+d[g,x]f,"Product Rule"]
};

higherRules={
  HoldPattern@d[InverseFunction[f_][x_],x_]:>dLabeled[1/dfunc[f,InverseFunction[f][x]],"Inverse Function Rule"],
  d[f_[g_],x_]/;g=!=x:>dLabeled[dfunc[f,g]d[g,x],"Chain Rule"],
  d[f_[g_,c_],x_]/;FreeQ[c,x]&&g=!=x:>dLabeled[dfunc[f[#,c]&,g]d[g,x],"Chain Rule"],
  d[f_[c_,g_],x_]/;FreeQ[c,x]&&g=!=x:>dLabeled[dfunc[f[c,#]&,g]d[g,x],"Chain Rule"]
};

substRules=dfunc[f_,g_]:>Module[{u},
  makeXForm[u];
  With[
    {df=dEval[dLabeled[f[u],Row@{"where ",TraditionalForm[u==g]}],u]},
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

allRules=Flatten@{
  transferRules,
  baseRules,
  functionRules,
  functionExtRules,
  substRules,
  higherRules
};


getLabels[expr_]:=With[
  {lbs=DeleteDuplicates@Cases[expr,dLabeled[_,lb_]:>lb,{0,Infinity}]},
  Row@Flatten@{"(",Riffle[lbs,"; "],")"}/;lbs=!={}
]
getLabels[_]="";

removeLabels[expr_]:=expr/.{dLabeled[e_,_]:>e}


$dDepth=0;

echoStep0[expr_]:=(
  CellPrint@Cell[BoxData[FormBox[ToBoxes[removeLabels@expr,TraditionalForm],TraditionalForm]],"Print",
    CellMargins->{{Inherited+20($dDepth-1), Inherited},{Inherited,Inherited}},
    CellFrameLabels->{{None,Cell[BoxData@ToBoxes@getLabels[expr],"MessageText"]},{None,None}}];
  expr
)

echoStep[expr_]:=(
  CellPrint@Cell[BoxData[FormBox[ToBoxes[removeLabels@expr,TraditionalForm],TraditionalForm]],"Print",
    CellDingbat->Cell["=","EchoLabel"],
    CellMargins->{{Inherited+20$dDepth, Inherited},{Inherited,Inherited}},
    CellFrameLabels->{{None,Cell[BoxData@ToBoxes@getLabels[expr],"MessageText"]},{None,None}}];
  expr
)


dEval[f_,x_]:=Block[{$dDepth=$dDepth+1},dEvalR[f,x]]
dEvalR[f_,x_]:=NestWhile[removeLabels@*echoStep@*ReplaceAll[allRules],removeLabels@echoStep0[d[f,x]],!FreeQ[#2,_d|_dfunc]&&UnsameQ[##]&,2]
stepD[f_,x_]:=With[{eval=dEval[f,x]},eval/;FreeQ[eval,_d|_dfunc]]


End[]


EndPackage[]
