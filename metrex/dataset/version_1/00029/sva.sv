// SVA checkers and binds for the given DUT

// MUX checker
module mux_2to1_sva (
  input a, input b, input sel, input mux_out
);
  // Functional correctness (sample after delta to avoid preponed sampling)
  assert property (@(a or b or sel or mux_out) 1'b1 |-> ##0 (mux_out == (sel ? b : a)));

  // Known-propagation: if inputs are known, output must be known
  assert property (@(a or b or sel or mux_out) ! $isunknown({a,b,sel}) |-> ##0 (! $isunknown(mux_out)));

  // Branch coverage
  cover property (@(a or b or sel) (sel==1'b0) ##0 (mux_out==a));
  cover property (@(a or b or sel) (sel==1'b1) ##0 (mux_out==b));
endmodule

// XOR checker
module xor_gate_sva (
  input xor_in1, input xor_in2, input xor_out
);
  // Functional correctness
  assert property (@(xor_in1 or xor_in2 or xor_out) 1'b1 |-> ##0 (xor_out == (xor_in1 ^ xor_in2)));

  // Known-propagation
  assert property (@(xor_in1 or xor_in2 or xor_out) ! $isunknown({xor_in1,xor_in2}) |-> ##0 (! $isunknown(xor_out)));

  // Truth-table coverage
  cover property (@(xor_in1 or xor_in2) ({xor_in1,xor_in2}==2'b00) ##0 (xor_out==1'b0));
  cover property (@(xor_in1 or xor_in2) ({xor_in1,xor_in2}==2'b01) ##0 (xor_out==1'b1));
  cover property (@(xor_in1 or xor_in2) ({xor_in1,xor_in2}==2'b10) ##0 (xor_out==1'b1));
  cover property (@(xor_in1 or xor_in2) ({xor_in1,xor_in2}==2'b11) ##0 (xor_out==1'b0));
endmodule

// Top-level checker
module top_module_sva (
  input a, input b, input sel, input z
);
  // End-to-end functional equivalence
  assert property (@(a or b or sel or z) 1'b1 |-> ##0 (z == ((sel ? b : a) ^ sel)));

  // Derived behavior checks
  assert property (@(a or b or sel or z) (sel==1'b0) |-> ##0 (z==a));
  assert property (@(a or b or sel or z) (sel==1'b1) |-> ##0 (z==~b));

  // Known-propagation: if inputs known, output must be known
  assert property (@(a or b or sel or z) ! $isunknown({a,b,sel}) |-> ##0 (! $isunknown(z)));

  // Input space coverage (all 8 combinations)
  genvar i;
  for (i=0; i<8; i++) begin : CMB
    localparam [2:0] V = i[2:0];
    cover property (@(a or b or sel) ##0 ({a,b,sel}==V));
  end
endmodule

// Bind checkers to DUT
bind mux_2to1   mux_2to1_sva   u_mux_2to1_sva   (.*);
bind xor_gate   xor_gate_sva   u_xor_gate_sva   (.*);
bind top_module top_module_sva u_top_module_sva (.*);