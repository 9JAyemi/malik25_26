// Bindable SVA checker for top_module
module top_module_sva (
  input  logic [3:0] in,
  input  logic       out_and,
  input  logic       out_or,
  input  logic       out_xor,
  // internal wires
  input  logic       and1, and2, and3, and4,
  input  logic       or1,  or2,
  input  logic       xor1
);
  default clocking cb @(*); endclocking

  // Internal wire correctness
  ap_and1:  assert property (and1 == (in[0] & in[1]));
  ap_and2:  assert property (and2 == (in[0] & in[2]));
  ap_and3:  assert property (and3 == (in[0] & in[3]));
  ap_and4:  assert property (and4 == (in[1] & in[2]));
  ap_or1:   assert property (or1  == (in[0] | in[1]));
  ap_or2:   assert property (or2  == (in[2] | in[3]));
  ap_xor1:  assert property (xor1 == (in[1] ^ in[3]));

  // Output correctness (vs internal wires and canonical forms)
  ap_out_and_w:  assert property (out_and == (and1 & and2 & and3 & and4));
  ap_out_and_r:  assert property (out_and == (&in));          // in[3]&in[2]&in[1]&in[0]
  ap_out_or_w:   assert property (out_or  == (or1 | or2));
  ap_out_or_r:   assert property (out_or  == (|in));          // in[3]|in[2]|in[1]|in[0]
  ap_out_xor_w:  assert property (out_xor == xor1);
  ap_out_xor_f:  assert property (out_xor == (in[1] ^ in[3]));

  // Simple logical consistency
  ap_and_implies_or: assert property (out_and |-> out_or);

  // Coverage: key corners and each output polarity
  cp_all_zero:  cover property (in == 4'b0000 && !out_or && !out_and && !out_xor);
  cp_all_one:   cover property (in == 4'b1111 &&  out_or &&  out_and);
  cp_onehot0:   cover property (in == 4'b0001);
  cp_onehot1:   cover property (in == 4'b0010);
  cp_onehot2:   cover property (in == 4'b0100);
  cp_onehot3:   cover property (in == 4'b1000);
  cp_out_or0:   cover property (!out_or);
  cp_out_or1:   cover property ( out_or);
  cp_out_and0:  cover property (!out_and);
  cp_out_and1:  cover property ( out_and);
  cp_out_xor0:  cover property (!out_xor); // in[1]==in[3]
  cp_out_xor1:  cover property ( out_xor); // in[1]!=in[3]

  // Internal wires can be 1
  cp_and1: cover property (and1);
  cp_and2: cover property (and2);
  cp_and3: cover property (and3);
  cp_and4: cover property (and4);
  cp_or1:  cover property (or1);
  cp_or2:  cover property (or2);
  cp_xor1: cover property (xor1);
endmodule

// Bind into the DUT (place in a separate SVA file or after the DUT definition)
bind top_module top_module_sva tmsva (
  .in(in),
  .out_and(out_and),
  .out_or(out_or),
  .out_xor(out_xor),
  .and1(and1), .and2(and2), .and3(and3), .and4(and4),
  .or1(or1), .or2(or2),
  .xor1(xor1)
);