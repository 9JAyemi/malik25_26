// SVA checker module for xor_const; bind to DUT for use.
module xor_const_sva #(parameter CONST = 32'hAAAAAAAA)
(
  input  logic [31:0] in,
  input  logic [31:0] out
);

  // Sample on any change of inputs/outputs (combinational DUT)
  default clocking cb @(in or out); endclocking

  // Static parameter checks
  initial begin
    assert ($bits(CONST) == 32) else $error("CONST must be 32 bits");
    assert (!$isunknown(CONST)) else $error("CONST contains X/Z");
  end

  // Functional correctness: out must equal in XOR CONST
  assert property (out == (in ^ CONST))
    else $error("xor_const: out != (in ^ CONST)");

  // Knownness: if input is known, output must be known
  assert property (!$isunknown(in) |-> !$isunknown(out))
    else $error("xor_const: produced X/Z on out from known in");

  // Coverage: key corner cases and bitwise mapping behavior
  cover property (in == 32'h0000_0000 && out == CONST);
  cover property (in == 32'hFFFF_FFFF && out == ~CONST);

  // Single-bit toggle on input causes same single-bit toggle on output
  cover property ($onehot(in ^ $past(in)) &&
                  ((out ^ $past(out)) == (in ^ $past(in))));

  // Multi-bit toggle mapping (any change)
  cover property ((in != $past(in)) &&
                  ((out ^ $past(out)) == (in ^ $past(in))));
endmodule

// Bind example:
// bind xor_const xor_const_sva #(.CONST(CONST)) xor_const_sva_i (.in(in), .out(out));