// SVA for Incrementer
// Bind this to the DUT; focuses on concise, high-quality checks and coverage.

module Incrementer_sva (input logic [3:0] in, input logic [3:0] out);

  // Sample whenever inputs change
  event in_change;
  always @(in) -> in_change;

  // Functional correctness: out == in + 1 (mod 16), allow 0-delay update
  assert property (@(in_change)
                   disable iff ($isunknown(in) || $isunknown(out))
                   ##0 (out == in + 4'd1))
    else $error("Incrementer mismatch: in=%0h out=%0h", in, out);

  // Known-in implies known-out (no X/Z propagation)
  assert property (@(in_change) !$isunknown(in) |-> ##0 !$isunknown(out))
    else $error("X/Z on out for known in: in=%0h out=%0h", in, out);

  // Full functional coverage of all 16 input→output mappings
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : C
      localparam int O = (v + 1) & 4'hF;
      cover property (@(in_change) ##0 (in == v[3:0] && out == O[3:0]));
    end
  endgenerate

  // Key boundary cases
  cover property (@(in_change) ##0 (in == 4'h0 && out == 4'h1));
  cover property (@(in_change) ##0 (in == 4'hE && out == 4'hF));
  cover property (@(in_change) ##0 (in == 4'hF && out == 4'h0)); // wrap

endmodule

bind Incrementer Incrementer_sva sva_inc (.in(in), .out(out));