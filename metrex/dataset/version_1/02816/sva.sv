// SVA for combinational_circuit: concise, functionally complete, with key coverage
// Bind inside the DUT to access internal wires.

module cc_sva(
  input  logic [3:0] in,
  input  logic       out_and,
  input  logic       out_or,
  input  logic       out_xor,
  input  logic [1:0] mux_out_and,
  input  logic [1:0] mux_out_or,
  input  logic [1:0] mux_out_xor
);

  // Leaf correctness (guarded against X on relevant inputs)
  assert property (!$isunknown(in[1:0]) |-> mux_out_and[0] == (in[0] & in[1]));
  assert property (!$isunknown(in[3:2]) |-> mux_out_and[1] == (in[2] & in[3]));

  assert property (!$isunknown(in[1:0]) |-> mux_out_or[0]  == (in[0] | in[1]));
  assert property (!$isunknown(in[3:2]) |-> mux_out_or[1]  == (in[2] | in[3]));

  assert property (!$isunknown(in[1:0]) |-> mux_out_xor[0] == (in[0] ^ in[1]));
  assert property (!$isunknown(in[3:2]) |-> mux_out_xor[1] == (in[2] ^ in[3]));

  // Output correctness vs. leaves (and reduction consistency)
  assert property (
    !$isunknown(in) |-> (
      (out_and == (mux_out_and[0] & mux_out_and[1])) &&
      (out_or  == (mux_out_or[0]  | mux_out_or[1]))  &&
      (out_xor == (mux_out_xor[0] ^ mux_out_xor[1])) &&
      (out_and == &in) &&
      (out_or  == |in) &&
      (out_xor == ^in)
    )
  );

  // No unknowns on outputs when inputs are known
  assert property (!$isunknown(in) |-> (! $isunknown(out_and) && ! $isunknown(out_or) && ! $isunknown(out_xor)));

  // Minimal yet meaningful coverage
  // Exercise both 0/1 on each output
  cover property (!$isunknown(in) &&  out_and);
  cover property (!$isunknown(in) && !out_and);
  cover property (!$isunknown(in) &&  out_or);
  cover property (!$isunknown(in) && !out_or);
  cover property (!$isunknown(in) &&  out_xor);
  cover property (!$isunknown(in) && !out_xor);

  // Exercise leaf terms hitting 1 at least once
  cover property (mux_out_and[0]);
  cover property (mux_out_and[1]);
  cover property (mux_out_or[0]);
  cover property (mux_out_or[1]);
  cover property (mux_out_xor[0]);
  cover property (mux_out_xor[1]);

  // Observe output toggles
  cover property ($rose(out_and));
  cover property ($fell(out_and));
  cover property ($rose(out_or));
  cover property ($fell(out_or));
  cover property ($rose(out_xor));
  cover property ($fell(out_xor));

endmodule

bind combinational_circuit cc_sva cc_sva_i(.*);