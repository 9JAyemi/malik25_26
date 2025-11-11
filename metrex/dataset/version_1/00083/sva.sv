// SVA checker for bitwise_or
// Bind this to the DUT and provide a sampling clock/reset from the TB.

module bitwise_or_sva #(parameter int W = 4) (
  input logic                 clk,
  input logic                 rst_n,
  input logic [W-1:0]         a,
  input logic [W-1:0]         b,
  input logic [W-1:0]         out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional correctness (4-state accurate)
  assert property (out === (a | b))
    else $error("bitwise_or mismatch: out != (a|b)");

  // No X/Z on output when inputs are known; also re-check with 2-state compare
  assert property (!$isunknown({a,b}) |-> (! $isunknown(out) && out == (a | b)))
    else $error("Known inputs must yield known correct out");

  // Output stability when inputs are stable
  assert property (($stable(a) && $stable(b)) |-> $stable(out))
    else $error("Out changed without input change");

  // Output changes only when the combinational function changes
  assert property ((out != $past(out)) |-> ((a | b) != $past(a | b)))
    else $error("Out toggled without cause");

  // Bit-level truth table implications (robust to X on unrelated bit)
  generate
    genvar i;
    for (i = 0; i < W; i++) begin : g_bit_tt
      assert property ( (a[i] === 1 || b[i] === 1) |-> (out[i] === 1) )
        else $error("OR truth-table fail: bit %0d should be 1", i);

      assert property ( (a[i] === 0 && b[i] === 0) |-> (out[i] === 0) )
        else $error("OR truth-table fail: bit %0d should be 0", i);

      // Truth-table coverage per bit
      cover property (a[i] == 0 && b[i] == 0 && out[i] == 0);
      cover property (a[i] == 0 && b[i] == 1 && out[i] == 1);
      cover property (a[i] == 1 && b[i] == 0 && out[i] == 1);
      cover property (a[i] == 1 && b[i] == 1 && out[i] == 1);
    end
  endgenerate

  // Vector-level coverage: extremes and transitions to/from all-zero
  cover property (out == '0);
  cover property (out == '1);
  cover property ($past(out) == '0 && out != '0);
  cover property ($past(out) != '0 && out == '0);

endmodule

// Example bind (connect clk/rst_n from your TB):
// bind bitwise_or bitwise_or_sva #(.W(4)) u_bitwise_or_sva (.*, .clk(tb_clk), .rst_n(tb_rst_n));