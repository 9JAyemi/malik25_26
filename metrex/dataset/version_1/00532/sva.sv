// SVA checker bound into mux4to1. Focused, high-quality functional checks and coverage.
module mux4to1_sva;
  // Access DUT signals directly (via bind)
  wire [1:0] sel = {S1,S0};
  wire d0 = ~S1 & ~S0;  // select A0
  wire d1 = ~S1 &  S0;  // select A1
  wire d2 =  S1 & ~S0;  // select A2
  wire d3 =  S1 &  S0;  // select A3

  // Power pins sanity
  ap_power: assert property (@(VPWR or VGND or VPB or VNB)
                             VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Basic X/Z checks on select and output
  ap_no_x_sel: assert property (@(S0 or S1) !$isunknown({S1,S0}));
  ap_no_x_y:   assert property (@(Y)        !$isunknown(Y));

  // Select decode must be one-hot
  ap_onehot_sel: assert property (@(S0 or S1) $onehot({d3,d2,d1,d0}));

  // Internal wires consistent with decode (helps debug)
  ap_w0: assert property (@(S0 or S1 or w0) w0 === d3);
  ap_w1: assert property (@(S0 or S1 or w1) w1 === d2);
  ap_w2: assert property (@(S0 or S1 or w2) w2 === d1);

  // Functional correctness: Y must equal selected input
  ap_mux: assert property (@(A0 or A1 or A2 or A3 or S0 or S1 or Y)
                           disable iff ($isunknown({S1,S0,A0,A1,A2,A3}))
                           Y === (sel==2'b00 ? A0 :
                                  sel==2'b01 ? A1 :
                                  sel==2'b10 ? A2 : A3));

  // Per-select pass-through checks
  ap_sel0: assert property (@(A0 or S0 or S1 or Y) d0 |-> (Y === A0));
  ap_sel1: assert property (@(A1 or S0 or S1 or Y) d1 |-> (Y === A1));
  ap_sel2: assert property (@(A2 or S0 or S1 or Y) d2 |-> (Y === A2));
  ap_sel3: assert property (@(A3 or S0 or S1 or Y) d3 |-> (Y === A3));

  // Coverage: exercise all select states and observe pass-through activity
  c_state_00: cover property (@(S0 or S1) d0);
  c_state_01: cover property (@(S0 or S1) d1);
  c_state_10: cover property (@(S0 or S1) d2);
  c_state_11: cover property (@(S0 or S1) d3);

  c_pass0: cover property (@(A0 or S0 or S1 or Y) d0 ##0 (Y===A0) ##0 $changed(A0));
  c_pass1: cover property (@(A1 or S0 or S1 or Y) d1 ##0 (Y===A1) ##0 $changed(A1));
  c_pass2: cover property (@(A2 or S0 or S1 or Y) d2 ##0 (Y===A2) ##0 $changed(A2));
  c_pass3: cover property (@(A3 or S0 or S1 or Y) d3 ##0 (Y===A3) ##0 $changed(A3));
endmodule

bind mux4to1 mux4to1_sva mux4to1_sva_i();