// SVA for top_module and its functionality (combinational design)
// Uses $global_clock for sampling; guards against Xs.

module top_module_sva (
  input  logic [15:0] a,
  input  logic [15:0] b,
  input  logic        sub,
  input  logic [31:0] mult_output,
  input  logic [15:0] sum_output,
  input  logic        xor_output
);
  default clocking cb @(posedge $global_clock); endclocking

  // No X/Z on outputs when inputs are known
  assert property (!$isunknown({a,b,sub}) |-> !$isunknown({mult_output,sum_output,xor_output}));

  // Multiplier functional equivalence
  assert property (!$isunknown({a,b,sub}) |-> mult_output == ($unsigned(a) * $unsigned(b)));

  // Adder functional equivalence (note: subtract path is a + ~b, no +1)
  assert property (!$isunknown({a,b,sub}) |-> sum_output == ($unsigned(a) + (sub ? ($unsigned(b) ^ 16'hFFFF) : $unsigned(b))));

  // XOR functional module and top-level bit extraction
  assert property (!$isunknown({a,b,sub}) |-> xor_output == (mult_output ^ {16'b0, sum_output})[0]);

  // Simple multiplier corner properties
  assert property (!$isunknown({a,b,sub}) && (a==16'h0) |-> mult_output==32'h0);
  assert property (!$isunknown({a,b,sub}) && (b==16'h0) |-> mult_output==32'h0);

  // Partial-product sanity: if b is one-hot at i, product equals a<<i
  genvar i;
  generate
    for (i=0;i<16;i++) begin : g_pp
      assert property (!$isunknown({a,b,sub}) && (b == (16'h1<<i)) |-> mult_output == ($unsigned(a) << i));
    end
  endgenerate

  // Minimal coverage
  cover property (sub==0);
  cover property (sub==1);
  cover property ($rose(sub));
  cover property ($fell(sub));
  cover property (a==16'h0000 && b==16'h0000);
  cover property (a==16'hFFFF && b==16'hFFFF);
  cover property (xor_output==0);
  cover property (xor_output==1);
  cover property ($countones(b) inside {[2:16]}); // exercise multi-bit partial products
endmodule

bind top_module top_module_sva top_module_sva_b (.*);