// SVA for bin2gray. Uses event-based sampling with ##0 to avoid preponed-region races.
module bin2gray_sva(input logic [3:0] in, input logic [3:0] out);

  // Sample on any input change
  default clocking cb @(in); endclocking

  // Functional equivalence (vector form)
  assert property (##0 (out == (in ^ {1'b0, in[3:1]})))
    else $error("bin2gray mismatch: in=%0h out=%0h exp=%0h", in, out, (in ^ {1'b0, in[3:1]}));

  // Known-in implies known-out
  assert property (!$isunknown(in) |-> ##0 !$isunknown(out))
    else $error("bin2gray X/Z on out with known in: in=%b out=%b", in, out);

  // Single-bit input change -> expected output bit changes
  assert property (
    ($changed(in[0]) && !$changed(in[1]) && !$changed(in[2]) && !$changed(in[3]))
    |-> ##0 ($changed(out[0]) && $changed(out[1]) && !$changed(out[2]) && !$changed(out[3]))
  );

  assert property (
    ($changed(in[1]) && !$changed(in[0]) && !$changed(in[2]) && !$changed(in[3]))
    |-> ##0 (!$changed(out[0]) && $changed(out[1]) && $changed(out[2]) && !$changed(out[3]))
  );

  assert property (
    ($changed(in[2]) && !$changed(in[0]) && !$changed(in[1]) && !$changed(in[3]))
    |-> ##0 (!$changed(out[0]) && !$changed(out[1]) && $changed(out[2]) && $changed(out[3]))
  );

  assert property (
    ($changed(in[3]) && !$changed(in[0]) && !$changed(in[1]) && !$changed(in[2]))
    |-> ##0 (!$changed(out[0]) && !$changed(out[1]) && !$changed(out[2]) && $changed(out[3]))
  );

  // Coverage: hit all input values
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : cov_in_vals
      cover property (##0 (in == v[3:0]));
    end
  endgenerate

  // Coverage: each output bit rises and falls at least once
  genvar b;
  generate
    for (b = 0; b < 4; b++) begin : cov_out_toggles
      cover property ($rose(out[b]));
      cover property ($fell(out[b]));
    end
  endgenerate

endmodule

// Bind into the DUT
bind bin2gray bin2gray_sva sva_inst(.*);