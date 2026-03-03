// SVA for ByteMuxOct — concise, priority-accurate, with focused coverage
module ByteMuxOct_sva (
  input logic [7:0] A_i, B_i, C_i, D_i, E_i, F_i, G_i, H_i,
  input logic       SAB_i, SC_i, SD_i, SE_i, SF_i, SG_i, SH_i,
  input logic [7:0] Y_o
);

  // Priority-gated select terms (H > G > F > E > D > C > B > A)
  let selH = SH_i;
  let selG = !SH_i && SG_i;
  let selF = !SH_i && !SG_i && SF_i;
  let selE = !SH_i && !SG_i && !SF_i && SE_i;
  let selD = !SH_i && !SG_i && !SF_i && !SE_i && SD_i;
  let selC = !SH_i && !SG_i && !SF_i && !SE_i && !SD_i && SC_i;
  let selB = !SH_i && !SG_i && !SF_i && !SE_i && !SD_i && !SC_i && SAB_i;
  let selA = !SH_i && !SG_i && !SF_i && !SE_i && !SD_i && !SC_i && !SAB_i;

  let Y_exp = ({8{selA}} & A_i) |
              ({8{selB}} & B_i) |
              ({8{selC}} & C_i) |
              ({8{selD}} & D_i) |
              ({8{selE}} & E_i) |
              ({8{selF}} & F_i) |
              ({8{selG}} & G_i) |
              ({8{selH}} & H_i);

  // Selects must be 0/1 (no X/Z)
  ap_no_x_sel: assert property (@(*)
    !$isunknown({SAB_i,SC_i,SD_i,SE_i,SF_i,SG_i,SH_i})
  );

  // Exactly one gated path active
  ap_onehot_sel: assert property (@(*)
    $onehot({selH,selG,selF,selE,selD,selC,selB,selA})
  );

  // Functional correctness of the mux
  ap_mux_correct: assert property (@(*)
    (Y_o == Y_exp)
  );

  // If the selected input is known, the output is known
  ap_known_out_when_selected_known: assert property (@(*)
    ((selA && !$isunknown(A_i)) ||
     (selB && !$isunknown(B_i)) ||
     (selC && !$isunknown(C_i)) ||
     (selD && !$isunknown(D_i)) ||
     (selE && !$isunknown(E_i)) ||
     (selF && !$isunknown(F_i)) ||
     (selG && !$isunknown(G_i)) ||
     (selH && !$isunknown(H_i))) |-> !$isunknown(Y_o)
  );

  // Coverage: exercise each selected source at least once
  cp_selA: cover property (@(*) selA);
  cp_selB: cover property (@(*) selB);
  cp_selC: cover property (@(*) selC);
  cp_selD: cover property (@(*) selD);
  cp_selE: cover property (@(*) selE);
  cp_selF: cover property (@(*) selF);
  cp_selG: cover property (@(*) selG);
  cp_selH: cover property (@(*) selH);

  // Coverage: exercise multi-select (priority override) scenarios
  cp_multi_select: cover property (@(*)
    ($countones({SAB_i,SC_i,SD_i,SE_i,SF_i,SG_i,SH_i}) >= 2)
  );

endmodule

// Bind into the DUT
bind ByteMuxOct ByteMuxOct_sva sva_inst (
  .A_i(A_i), .B_i(B_i), .C_i(C_i), .D_i(D_i),
  .E_i(E_i), .F_i(F_i), .G_i(G_i), .H_i(H_i),
  .SAB_i(SAB_i), .SC_i(SC_i), .SD_i(SD_i), .SE_i(SE_i),
  .SF_i(SF_i), .SG_i(SG_i), .SH_i(SH_i),
  .Y_o(Y_o)
);