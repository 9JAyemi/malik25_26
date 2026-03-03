// SVA for binary_to_gray. Sampled on an external clock.
// Bind example (assuming clk,rst_n exist in your TB):
// bind binary_to_gray binary_to_gray_sva #(.W(4)) u_sva (.* , .clk(clk), .rst_n(rst_n));

module binary_to_gray_sva #(parameter int W=4)
(
  input  logic              clk,
  input  logic              rst_n,
  input  logic [W-1:0]      bin_in,
  input  logic [W-1:0]      gray_out
);

  default clocking @(posedge clk); endclocking

  function automatic logic [W-1:0] gray_exp (input logic [W-1:0] b);
    return (b >> 1) ^ b;
  endfunction

  let past_ok      = $past(rst_n);
  let toggle_i     = bin_in   ^ $past(bin_in);
  let toggle_o     = gray_out ^ $past(gray_out);

  // Functional correctness
  a_vec_eq: assert property (disable iff (!rst_n)
    !$isunknown(bin_in) |-> (gray_out == gray_exp(bin_in))
  );

  // No X/Z on output when input is clean
  a_no_x: assert property (disable iff (!rst_n)
    !$isunknown(bin_in) |-> !$isunknown(gray_out)
  );

  // Purely combinational: no output change if input is unchanged
  a_stable: assert property (disable iff (!rst_n)
    past_ok && (bin_in == $past(bin_in)) |-> (gray_out == $past(gray_out))
  );

  // Dynamic toggle behavior: single input-bit flip causes:
  // - 1 output bit flip if LSB (bit 0) flipped
  // - 2 output bit flips otherwise
  a_1hot_toggle_resp: assert property (disable iff (!rst_n)
    past_ok && $onehot(toggle_i) |->
      ($countones(toggle_o) == (toggle_i[0] ? 1 : 2))
  );

  // Input space coverage (all 2^W values)
  genvar v;
  generate
    for (v = 0; v < (1<<W); v++) begin: C_IN_VALS
      c_in_vals: cover property (rst_n && (bin_in == v[W-1:0]));
    end
  endgenerate

  // Output space coverage (all 2^W Gray values)
  genvar g;
  generate
    for (g = 0; g < (1<<W); g++) begin: C_OUT_VALS
      c_out_vals: cover property (rst_n && (gray_out == g[W-1:0]));
    end
  endgenerate

  // Single-bit input toggle coverage per bit
  genvar i;
  generate
    for (i = 0; i < W; i++) begin: C_TOGGLE_IN
      c_tgl_in: cover property (past_ok && $onehot(toggle_i) && toggle_i[i]);
    end
  endgenerate

endmodule