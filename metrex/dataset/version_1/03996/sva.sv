// SVA checker for ones_complement
module ones_complement_sva #(parameter WIDTH = 4) (
  input logic [WIDTH-1:0] in,
  input logic [WIDTH-1:0] out
);

  // Functional correctness (4-state accurate), sampled on any change; check after delta
  assert property (@(in or out) 1'b1 |-> ##0 (out === ~in))
    else $error("ones_complement mismatch: out=%0h, expected ~in=%0h", out, ~in);

  // If an input bit is known, the corresponding output bit must be known and the inverse
  genvar i;
  for (i = 0; i < WIDTH; i++) begin : A_KNOWN_PER_BIT
    assert property (@(in or out) !$isunknown(in[i]) |-> ##0 (! $isunknown(out[i]) && (out[i] == ~in[i])))
      else $error("Bit %0d knownness/inversion violated: in=%b out=%b", i, in[i], out[i]);
  end

  // Coverage: hit all input values and their mapped outputs
  genvar v;
  for (v = 0; v < (1<<WIDTH); v++) begin : C_ALL_VALS
    localparam logic [WIDTH-1:0] VAL = v[WIDTH-1:0];
    cover property (@(in) ##0 (in == VAL && out === ~in));
  end

  // Coverage: each bit’s 0->1 and 1->0 toggle causes opposite toggle on out in same delta
  for (i = 0; i < WIDTH; i++) begin : C_TOGGLES
    cover property (@(in[i]) $rose(in[i]) ##0 $fell(out[i]));
    cover property (@(in[i]) $fell(in[i]) ##0 $rose(out[i]));
  end

endmodule

// Bind example:
// bind ones_complement ones_complement_sva #(.WIDTH(4)) ones_complement_sva_i (.in(in), .out(out));