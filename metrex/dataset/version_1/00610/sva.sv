// SVA checker for accumulator: out == popcount(in), fully covered, concise.

module accumulator_sva #(parameter int n = 4)
(
  input  logic              clk,
  input  logic              rst_n,
  input  logic [n-1:0]      in,
  input  logic [n:0]        out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z after reset
  ap_no_x:        assert property (!$isunknown({in,out}));

  // Core functionality: population count
  ap_popcount:    assert property ($unsigned(out) == $countones(in));

  // Range check (guards overflow)
  ap_range:       assert property ($unsigned(out) <= n);

  // Combinational consistency: if inputs don’t change, output doesn’t change
  ap_stable:      assert property ($stable(in) |-> $stable(out));

  // Coverage: hit every possible sum 0..n
  generate
    genvar k;
    for (k = 0; k <= n; k++) begin : C_SUMS
      cp_sum_k: cover property ($unsigned(out) == k);
    end
  endgenerate

  // Coverage: observe single-bit input toggle events
  cp_onebit_toggle: cover property ($onehot(in ^ $past(in)));

endmodule

// Example bind (hook to your environment clock/reset):
// bind accumulator accumulator_sva #(.n(n)) u_acc_sva (.clk(tb_clk), .rst_n(tb_rst_n), .in(in), .out(out));

// Optional purely combinational immediate-assert version if no clock is available
module accumulator_sva_comb #(parameter int n = 4)
(
  input  logic [n-1:0] in,
  input  logic [n:0]   out
);
  always_comb begin
    assert (!$isunknown({in,out})) else $error("accumulator: X/Z on ports");
    assert ($unsigned(out) == $countones(in)) else $error("accumulator: out != popcount(in)");
    assert ($unsigned(out) <= n) else $error("accumulator: out exceeds n");
  end
endmodule
// Example bind:
// bind accumulator accumulator_sva_comb #(.n(n)) u_acc_sva_comb (.in(in), .out(out));