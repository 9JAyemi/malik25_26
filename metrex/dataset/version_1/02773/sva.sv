// SVA bind module for bitwise_operation
module bitwise_operation_assert (
  input logic [7:0] a_in,
  input logic [7:0] b_in,
  input logic [7:0] out
);

  // Combinational correctness (clockless concurrent assertions)
  assert property (out[7:2] == a_in[7:2]);
  assert property (out[1]   == (a_in[1] ^~ b_in[1]));
  assert property (out[0]   == (a_in[0]  ^ b_in[0]));

  // Outputs known when inputs are known
  assert property (!$isunknown({a_in,b_in}) |-> !$isunknown(out));

  // Independence: upper bits unaffected by b_in changes
  assert property ($changed(b_in[7:2]) && $stable(a_in) |-> $stable(out[7:2]));

  // Coverage: exercise both XOR/XNOR outcomes
  cover property (!$isunknown({a_in[1],b_in[1]}) && (a_in[1] == b_in[1]) && out[1]==1);
  cover property (!$isunknown({a_in[1],b_in[1]}) && (a_in[1] != b_in[1]) && out[1]==0);
  cover property (!$isunknown({a_in[0],b_in[0]}) && (a_in[0] ^  b_in[0]) && out[0]==1);
  cover property (!$isunknown({a_in[0],b_in[0]}) && !(a_in[0] ^ b_in[0]) && out[0]==0);

  // Coverage: upper-bit pass-through toggles observed
  genvar i;
  generate
    for (i=2; i<8; i++) begin : C_UPPER_TOGGLE
      cover property (!$isunknown(a_in[i]) && $changed(a_in[i]) && (out[i]==a_in[i]));
    end
  endgenerate

endmodule

// Bind into DUT
bind bitwise_operation bitwise_operation_assert u_bitwise_operation_assert(.a_in(a_in), .b_in(b_in), .out(out));