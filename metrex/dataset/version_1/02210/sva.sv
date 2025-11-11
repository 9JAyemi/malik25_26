// SVA for MULT18X18S
module MULT18X18S_sva (
  input  logic                 C,
  input  logic                 R,
  input  logic                 CE,
  input  logic signed [17:0]   A,
  input  logic signed [17:0]   B,
  input  logic signed [35:0]   P
);

  default clocking cb @(posedge C); endclocking

  // Basic X checks
  a_ctrl_no_x:            assert property (!$isunknown({R,CE}));
  a_inputs_no_x_when_ce:  assert property (CE && !R |-> !$isunknown({A,B}));

  // Functional correctness
  a_sync_reset:    assert property (R |=> P == 36'sd0);
  a_ce_update:     assert property (!R && CE |=> P === ($signed(A) * $signed(B)));
  a_hold_no_ce:    assert property (!R && !CE |=> P === $past(P));
  // Optional sign consistency when not multiplying by zero
  a_sign_check:    assert property (!R && CE && (A!=0) && (B!=0) |=> P[35] == (A[17] ^ B[17]));

  // P should be known after any update (reset or CE)
  a_p_known_after_update: assert property ( (R || (!R && CE)) |=> !$isunknown(P) );

  // Coverage
  c_reset:           cover property (R |=> P==36'sd0);
  c_ce_mul:          cover property (!R && CE |=> P === ($signed(A) * $signed(B)));
  c_hold:            cover property (!R && !CE ##1 $stable(P));
  c_back_to_back_ce: cover property (!R && CE ##1 !R && CE);

endmodule

bind MULT18X18S MULT18X18S_sva sva_inst (.*);