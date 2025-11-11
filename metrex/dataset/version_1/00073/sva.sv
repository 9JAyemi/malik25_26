// SVA checker for pass_through
// Bind this to the DUT to verify behavior and collect coverage.

module pass_through_sva #(parameter WIDTH = 8)
(
  input  logic              vdd18,
  input  logic [WIDTH-1:0]  in,
  input  logic [WIDTH-1:0]  out
);

  // Core functional equivalence (combinational, X-sensitive)
  always_comb begin
    assert (out === (vdd18 ? in : '0))
      else $error("pass_through mismatch: vdd18=%b in=%0h out=%0h", vdd18, in, out);
  end

  // Sanity on supply and X-propagation expectations
  // vdd18 must be 0/1 (no X/Z)
  always_comb begin
    assert (!$isunknown(vdd18))
      else $error("vdd18 is X/Z");
  end

  // When vdd18==0, out must be exactly zero (even if in is X)
  always_comb if (vdd18===1'b0) assert (out === '0)
    else $error("out not zero when vdd18=0: out=%0h", out);

  // When vdd18==1 and in is known, out must equal in and be known
  always_comb if (vdd18===1'b1 && !$isunknown(in)) assert (out === in && !$isunknown(out))
    else if (vdd18===1'b1 && !$isunknown(in)) $error("out!=in when vdd18=1: in=%0h out=%0h", in, out);

  // Lightweight coverage
  // Power toggles
  cover property (@(posedge vdd18) 1);
  cover property (@(negedge vdd18) 1);

  // Masking active: in nonzero while power off, out held at 0
  cover property (@(in or vdd18 or out) (vdd18==1'b0 && in!= '0 && out=='0));

  // Pass-through active: in nonzero while power on, out equals in
  cover property (@(in or vdd18 or out) (vdd18==1'b1 && in!= '0 && out==in));

  // Per-bit observation: each bit can be masked low and passed high
  genvar i;
  generate for (i=0;i<WIDTH;i++) begin : g_cov_bits
    cover property (@(in[i] or vdd18 or out[i]) (vdd18==1'b0 && in[i]==1'b1 && out[i]==1'b0));
    cover property (@(in[i] or vdd18 or out[i]) (vdd18==1'b1 && in[i]==1'b1 && out[i]==1'b1));
  end endgenerate

endmodule

// Bind into the DUT
bind pass_through pass_through_sva #(.WIDTH(8)) u_pass_through_sva (
  .vdd18(vdd18),
  .in(in),
  .out(out)
);