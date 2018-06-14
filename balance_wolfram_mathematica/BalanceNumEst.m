(* ::Package:: *)

(*
    Returns incidence matrix of d-bonacciho substitution
        alphabetCardinality - alphabet cardinality d
*)
incidenceMatrix[alphabetCardinality_] :=
    incidenceMatrix[alphabetCardinality] =
    Module[ {},
        Assert[IntegerQ[alphabetCardinality]];
        Assert[alphabetCardinality > 1];
        Join[
            {ParallelSum[UnitVector[alphabetCardinality, i], {i, alphabetCardinality}]},
            Table[UnitVector[alphabetCardinality, i], {i, alphabetCardinality - 1}]
        ]
    ];

(*
    Returns spectrum of incidence matrix of d-bonacciho substitution
        alphabetCardinality - alphabet cardinality d
*)
sortedSpectrum[alphabetCardinality_] :=
    sortedSpectrum[alphabetCardinality] =
    Module[ {},
        Assert[IntegerQ[alphabetCardinality]];
        Assert[alphabetCardinality > 1];
        Sort[ 
            Eigenvalues[incidenceMatrix[alphabetCardinality]],
            N[Abs[#1],1000] >= N[Abs[#2],1000] &
         ]
    ]

dominatingEigenvalue[alphabetCardinality_] :=
    dominatingEigenvalue[alphabetCardinality] =
    Module[ {},
        Assert[IntegerQ[alphabetCardinality]];
        Assert[alphabetCardinality > 1];
        (sortedSpectrum[alphabetCardinality])[[1]]
    ]

(*
    Returns vector of letter frequencies \mu
        incidenceMatrix - incidence matrix M_\varphi
*)
frequenciesVector[alphabetCardinality_] :=
    frequenciesVector[alphabetCardinality] = 
    Module[ {},
        Assert[IntegerQ[alphabetCardinality]];
        Assert[alphabetCardinality > 1];
        ((Eigenvectors[incidenceMatrix[alphabetCardinality], 1][[1]]) / (ParallelSum[
                Eigenvectors[incidenceMatrix[alphabetCardinality], 1][[1]][[i]],
                {i, 1, alphabetCardinality}
            ]))//FullSimplify
    ];

(*
    Returns vector f_a
        letter - letter a
        frequenciesVector - vector of letter frequencies \mu
*)
faVector[alphabetCardinality_, letter_] :=
    faVector[alphabetCardinality, letter] = 
    Module[ {},
        Assert[IntegerQ[alphabetCardinality]];
        Assert[IntegerQ[letter]];
        Assert[0 <= letter <= alphabetCardinality - 1];
        (Table[
            -frequenciesVector[[alphabetCardinality]][[letter + 1]],
            {alphabetCardinality}
        ] + UnitVector[alphabetCardinality, letter + 1]) // FullSimplify
    ];

(*
    Returns T_n - n-th member of the d-bonacci sequence where T_ 0 = ... = T_{d-2} = 0, T_{d-1} = 1
        d - cardinality of alphabet
        nr - number of member to be returned
*)
dBSeq[alphabetCardinality_,nr_] :=
    dBSeq[alphabetCardinality,nr] = 
    Module[ {},
        Assert[IntegerQ[alphabetCardinality]];
        Assert[IntegerQ[nr]];
        Assert[alphabetCardinality > 1];
        Assert[nr >= 0];
        If[ nr<alphabetCardinality,
            If[ nr==alphabetCardinality-1,
                1,
                0
            ],
            Sum[dBSeq[alphabetCardinality,i],{i,nr-alphabetCardinality,nr-1}]
        ]
    ];

dBLens[alphabetCardinality_,nr_] :=
    dBLens[alphabetCardinality,nr] = 
		Sum[UnitVector[alphabetCardinality,i],{i,1,alphabetCardinality} ].
		MatrixPower[incidenceMatrix[alphabetCardinality],nr] .
		UnitVector[alphabetCardinality,1];


g[alphabetCardinality_, letter_, exponent_, OptionsPattern[]] :=
    g[alphabetCardinality, letter, exponent, OptionsPattern[]] =
    Module[ {},
        Assert[IntegerQ[alphabetCardinality]];
        Assert[IntegerQ[letter]];
        Assert[0 <= letter <= alphabetCardinality - 1];
        dBSeq[alphabetCardinality, exponent+alphabetCardinality-1-letter] - 
                dominatingEigenvalue[alphabetCardinality]^(-1-letter) *
                dBSeq[alphabetCardinality, exponent+alphabetCardinality]
    ];

    
gRek[alphabetCardinality_, exponent_, OptionsPattern[]] :=
    gRek[alphabetCardinality, exponent, OptionsPattern[]] =
    Module[ {},
        Assert[IntegerQ[alphabetCardinality]];
        Assert[alphabetCardinality > 1];
        If[ exponent<alphabetCardinality,
            UnitVector[alphabetCardinality,exponent+1],
            Sum[gRek[alphabetCardinality,exponent-i],{i,alphabetCardinality}]
        ]
    ];

errorConstant[alphabetCardinality_,letter_] :=
    Module[ {spec,pol,polDer},
        spec = sortedSpectrum[alphabetCardinality];
        pol = Product[#-spec[[i]],{i,1,alphabetCardinality}]&;
        polDer = D[pol[x],x];
        Sum[            
        	Abs[
            	(1/( spec[[j]] ^ (letter + 1) ) - 1/( spec[[1]] ^ (letter + 1) )) *
                (1 / ( polDer /. x -> spec[[j]])) * 
                (Abs[spec[[j]]] ^ (alphabetCardinality))
            ] / (1 - Abs[spec[[j]]]),
            {j,2,alphabetCardinality}
        ]
    ];
    
beta2abs[alphabetCardinality_] :=
    beta2abs[alphabetCardinality] = 
    Abs[sortedSpectrum[alphabetCardinality][[2]]];  

sgn[expr_]:=
	sgn[expr]=
	Sign[expr];

sgn2[expr_]:=
sgn2[expr]=
	If[sgn[expr]==1,1,0]

(*
	EXTREMALNI FAKTOR
*)

integerCombinationVector[alphabetCardinality_,letter_,membersToSum_]:=
	integerCombinationVector[alphabetCardinality,letter,membersToSum]=
	Sum[sgn[g[alphabetCardinality,letter,i]] * gRek[alphabetCardinality,i],{i,0,membersToSum-1}];

integerCombinationResultSym[alphabetCardinality_,letter_,membersToSum_]:=
	integerCombinationResultSym[alphabetCardinality,letter,membersToSum]=
	integerCombinationVector[alphabetCardinality,letter,membersToSum] . Table[g[alphabetCardinality,letter,i],{i,0,alphabetCardinality - 1}] // Expand;

integerCombinationResultNum[alphabetCardinality_,letter_,membersToSum_,precision_]:=
	integerCombinationResultNum[alphabetCardinality,letter,membersToSum,precision]=
	N[integerCombinationResultSym[alphabetCardinality,letter,membersToSum],{Infinity,precision}];

estimatedError[alphabetCardinality_,letter_,membersToSum_,precision_]:=
	N[errorConstant[alphabetCardinality,letter] * (beta2abs[alphabetCardinality] ^ membersToSum) ,{Infinity,precision}];

integerCombinationResultNumPlusErr[alphabetCardinality_,letter_,membersToSum_,precision_]:=
	integerCombinationResultNum[alphabetCardinality,letter,membersToSum,precision] + (11.0/10.0)*estimatedError[alphabetCardinality,letter,membersToSum,precision];

balance[alphabetCardinality_,letter_,membersToSum_,precision_]:=
	Block[{},
		Assert[Floor[2* integerCombinationResultNum[alphabetCardinality,letter,membersToSum,precision]]==Floor[2* integerCombinationResultNumPlusErr[alphabetCardinality,letter,membersToSum,precision]]];
		Floor[2* integerCombinationResultNum[alphabetCardinality,letter,membersToSum,precision]]
	];

extremalBalanceFactor[d_,letter_,iMax_]:=
	Block[{m,n},
		m = Sum[dBLens[d,i]*sgn2[g[d,letter,i]],{i,0,iMax}];
		n = Sum[dBLens[d,i]*sgn2[-g[d,letter,i]],{i,0,iMax}];
		{Min[m,n],Max[m,n]}
	];

getUNormalRepr[dd_, n_] := 
getUNormalRepr[dd, n] = 
  Module[{exponentMax, remainder, coefficient},
   remainder = n;
   exponentMax = 0;
   While[dBLens[dd, exponentMax] <= n, exponentMax++;];
   exponentMax--;
   
   Table[
    coefficient = Quotient[remainder, dBLens[dd, exponentMax - i]];
    remainder = Mod[remainder, dBLens[dd, exponentMax - i]];
    coefficient,
    {i, 0, exponentMax}
    ]
   ];

prefixDiscrepancy[alphabetCardinality_, letter_, prefixLength_] := 
prefixDiscrepancy[alphabetCardinality, letter, prefixLength] = 
Block[{repr},
   repr = getUNormalRepr[alphabetCardinality, prefixLength];
   Sum[g[alphabetCardinality, letter, i] * repr[[-i-1]], {i, 0, Length[repr] - 1}]
   ];
   
factorDiscrepancy[alphabetCardinality_,letter_,n1_,n2_] := Block[{nn1,nn2},
   {nn1,nn2} = {Min[n1,n2],Max[n1,n2]};
   prefixDiscrepancy[alphabetCardinality,letter,nn2] - prefixDiscrepancy[alphabetCardinality,letter,nn1] 
];
