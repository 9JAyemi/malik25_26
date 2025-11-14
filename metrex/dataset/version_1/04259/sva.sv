// SVA checker for my_module
module my_module_sva (
  input logic Y,
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);

  // Fire on any input edge; use ##0 to avoid race with combinational updates
  default clocking cb @(posedge A1 or negedge A1 or
                         posedge A2 or negedge A2 or
                         posedge B1_N or negedge B1_N);
  endclocking

  // Functional equivalence
  ap_func: assert property (1'b1 |-> ##0
    (Y === ((~A1 & A2) | (A1 & ~A2) | (~A1 & ~A2 & ~B1_N)))
  );

  // Partitioned, readable checks
  ap_xor: assert property ((A1 ^ A2) |-> ##0 (Y === 1'b1));
  ap_00 : assert property ((~A1 & ~A2) |-> ##0 (Y === ~B1_N));
  ap_11 : assert property (( A1 &  A2) |-> ##0 (Y === 1'b0));

  // Knownness: if inputs known, output must be known
  ap_known: assert property ((!$isunknown({A1,A2,B1_N})) |-> ##0 (!$isunknown(Y)));

  // Supplies hold expected values
  ap_supplies: assert property (1'b1 |-> (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0));

  // Y changes only when an input changes (no spurious glitches)
  ap_y_change_caused_by_inputs: assert property (@(posedge Y or negedge Y)
    ($changed(A1) || $changed(A2) || $changed(B1_N))
  );

  // Coverage: hit all functional regions and both Y polarities
  cv_xor  : cover property ((A1 ^ A2) ##0 (Y==1'b1));
  cv_00_b1: cover property ((~A1 & ~A2 &  B1_N) ##0 (Y==1'b0));
  cv_00_nb: cover property ((~A1 & ~A2 & ~B1_N) ##0 (Y==1'b1));
  cv_11   : cover property (( A1 &  A2) ##0 (Y==1'b0));
  cv_y_r  : cover property (@(posedge Y) 1);
  cv_y_f  : cover property (@(negedge Y) 1);

endmodule

// Bind the checker to the DUT
bind my_module my_module_sva sva_i (
  .Y(Y), .A1(A1), .A2(A2), .B1_N(B1_N),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);