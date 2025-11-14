// SVA checker for xor_multiplexer_4bit
module xor_multiplexer_4bit_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       sel,
  input logic [3:0] out
);
  default clocking cb @(*); endclocking

  // Functional equivalence (vector-level)
  a_func: assert property (1'b1 |-> ##0 (out == (a ^ ({4{sel}} & b))));

  // Knownness: if inputs are known, output is known in same timestep
  a_known: assert property (!$isunknown({a,b,sel}) |-> ##0 !$isunknown(out));

  // Combinational stability: if inputs don't change, output doesn't change
  a_stable: assert property ($stable({a,b,sel}) |-> ##0 $stable(out));

  // Useful conditional simplifications (debug-friendly)
  a_sel0: assert property (!sel |-> ##0 (out == a));
  a_sel1: assert property ( sel |-> ##0 (out == (a ^ b)));

  // Coverage: exercise both paths and each XOR bit effect
  c_sel0:  cover property (!sel && (out == a));
  c_sel1:  cover property ( sel && (out == (a ^ b)));
  genvar i;
  generate
    for (i=0;i<4;i++) begin : C_BIT
      c_xor_bit: cover property (sel && b[i] && (out[i] != a[i]));
    end
  endgenerate
endmodule

// Bind example:
// bind xor_multiplexer_4bit xor_multiplexer_4bit_sva u_xor_multiplexer_4bit_sva(.a(a), .b(b), .sel(sel), .out(out));