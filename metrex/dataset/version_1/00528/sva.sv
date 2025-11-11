// SVA for bitwise_and: concise, high-quality checks with full functional coverage.
// Bind this checker to the DUT.

module bitwise_and_sva #(parameter int WIDTH = 4)
(
  input  logic [WIDTH-1:0] in1,
  input  logic [WIDTH-1:0] in2,
  input  logic [WIDTH-1:0] out,
  input  logic             VPWR, VGND, VPB, VNB
);

  // Static sanity
  initial begin
    assert (WIDTH == 4) else $error("bitwise_and_sva: expected WIDTH=4");
  end

  // Helper for power-good gating
  function automatic bit power_good();
    return (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === 1'b1) && (VNB === 1'b0);
  endfunction

  // Immediate assertions (combinational)
  always_comb begin
    bit pgood = power_good();

    // Functional spec: AND
    assert (!pgood || (out === (in1 & in2)))
      else $error("AND mismatch: out=%0h in1=%0h in2=%0h", out, in1, in2);

    // De Morgan equivalence (consistency with implementation style)
    assert (!pgood || ((~out) === ((~in1) | (~in2))))
      else $error("DeMorgan mismatch: ~out=%0h ~(in1)|~(in2)=%0h", ~out, ((~in1)|(~in2)));

    // No X/Z on out when inputs are known and power is good
    if (pgood && !$isunknown(in1) && !$isunknown(in2)) begin
      assert (!$isunknown(out))
        else $error("X/Z on out with known inputs: in1=%0h in2=%0h out=%0h", in1, in2, out);
    end
  end

  // Per-bit truth-table coverage (all 4 cases per bit)
  genvar i;
  generate for (i = 0; i < WIDTH; i++) begin : g_cov
    always_comb if (power_good()) begin
      cover (in1[i] === 1'b0 && in2[i] === 1'b0 && out[i] === 1'b0);
      cover (in1[i] === 1'b0 && in2[i] === 1'b1 && out[i] === 1'b0);
      cover (in1[i] === 1'b1 && in2[i] === 1'b0 && out[i] === 1'b0);
      cover (in1[i] === 1'b1 && in2[i] === 1'b1 && out[i] === 1'b1);
    end
  end endgenerate

endmodule

// Bind to all instances of bitwise_and
bind bitwise_and bitwise_and_sva #(.WIDTH(4)))
  bitwise_and_sva_i (.*);