// SVA for BOOL_EXP
module BOOL_EXP_sva (
  input logic A,
  input logic B,
  input logic OUT
);
  // Sample on any input edge (combinational block)
  default clocking cb @(posedge A or negedge A or posedge B or negedge B); endclocking

  // No X on OUT when inputs are known
  assert_no_x_out: assert property ( !$isunknown({A,B}) |-> !$isunknown(OUT) );

  // Functional correctness (simplified)
  assert_func_simplified: assert property ( disable iff ($isunknown({A,B,OUT})) OUT == (~A & B) );

  // Functional correctness (as written)
  assert_func_original: assert property ( disable iff ($isunknown({A,B,OUT}))
                                          OUT == ((A & ~(B | A)) | (~A & B)) );

  // Absorption: A & ~(B|A) is 0 for 2-state inputs
  assert_absorption: assert property ( disable iff ($isunknown({A,B})) (A & ~(B | A)) == 1'b0 );

  // Full truth-table coverage
  cover_tt00: cover property ( disable iff ($isunknown({A,B,OUT})) (!A && !B && OUT==0) );
  cover_tt01: cover property ( disable iff ($isunknown({A,B,OUT})) (!A &&  B && OUT==1) );
  cover_tt10: cover property ( disable iff ($isunknown({A,B,OUT})) ( A && !B && OUT==0) );
  cover_tt11: cover property ( disable iff ($isunknown({A,B,OUT})) ( A &&  B && OUT==0) );

  // Output toggle coverage
  cover_rise: cover property ( disable iff ($isunknown({A,B,OUT})) $rose(OUT) );
  cover_fall: cover property ( disable iff ($isunknown({A,B,OUT})) $fell(OUT) );
endmodule

// Bind into DUT
bind BOOL_EXP BOOL_EXP_sva sva_BOOL_EXP(.A(A), .B(B), .OUT(OUT));