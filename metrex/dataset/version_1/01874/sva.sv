// SVA for and_pg
module and_pg_sva(input logic A, B, PG);

  // Sample on any input edge
  default clocking cb @ (posedge A or negedge A or posedge B or negedge B); endclocking

  // Functional equivalence (4-state accurate)
  ap_func: assert property (PG === (A & B));

  // If inputs known, output must be known
  ap_known_out: assert property (!$isunknown({A,B}) |-> !$isunknown(PG));

  // Zero dominance
  ap_zero_dom_A: assert property ((A === 1'b0) |-> (PG === 1'b0));
  ap_zero_dom_B: assert property ((B === 1'b0) |-> (PG === 1'b0));

  // PG=1 implies both inputs are 1
  ap_one_implies_both_one: assert property ((PG === 1'b1) |-> (A === 1'b1 && B === 1'b1));

  // PG can only change when at least one input changes
  ap_pg_change_has_cause: assert property (@(posedge PG or negedge PG) !$stable({A,B}));

  // Truth-table coverage
  cp_00: cover property (A===1'b0 && B===1'b0 && PG===1'b0);
  cp_01: cover property (A===1'b0 && B===1'b1 && PG===1'b0);
  cp_10: cover property (A===1'b1 && B===1'b0 && PG===1'b0);
  cp_11: cover property (A===1'b1 && B===1'b1 && PG===1'b1);

  // Output toggle coverage
  cpg_rise: cover property (@(posedge PG) 1);
  cpg_fall: cover property (@(negedge PG) 1);

endmodule

bind and_pg and_pg_sva u_and_pg_sva(.A(A), .B(B), .PG(PG));