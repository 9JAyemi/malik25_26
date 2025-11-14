// SVA checker for XC2COrArray
// Sampled on an external clk; bind this module to the DUT.
module xc2c_or_array_sva #(parameter int W = 56, N = 16)
(
  input  logic                   clk,
  input  logic [W-1:0]           pterms_in,
  input  logic [N*W-1:0]         config_bits,
  input  logic [N-1:0]           or_out
);

  // X-prop and stability sanity
  ap_no_x: assert property (@(posedge clk)
    !$isunknown({pterms_in, config_bits}) |-> !$isunknown(or_out)
  );

  ap_stable: assert property (@(posedge clk)
    $stable({pterms_in, config_bits}) |-> $stable(or_out)
  );

  genvar n;
  for (n = 0; n < N; n++) begin : g_or
    wire [W-1:0] mask_n = ~config_bits[n*W +: W];     // 1 = enabled pterm
    wire         exp_n  = |(pterms_in & mask_n);

    // Functional equivalence: or_out[n] == OR of enabled pterms
    ap_eq: assert property (@(posedge clk) or_out[n] == exp_n)
      else $error("XC2COrArray or_out[%0d] mismatch", n);

    // Corner cases
    ap_all_disabled_zero: assert property (@(posedge clk)
      (mask_n == '0) |-> (or_out[n] == 1'b0)
    );

    ap_all_enabled_reduce: assert property (@(posedge clk)
      (mask_n == '1) |-> (or_out[n] == (|pterms_in))
    );

    // Coverage
    cp_hi:   cover property (@(posedge clk) (mask_n != '0) && exp_n && or_out[n]);
    cp_lo:   cover property (@(posedge clk) (or_out[n] == 1'b0));
    cp_rise: cover property (@(posedge clk) $rose(or_out[n]));
    cp_fall: cover property (@(posedge clk) $fell(or_out[n]));
  end

  // Global coverage: any output high, all outputs low
  cp_any_hi:  cover property (@(posedge clk) (|or_out));
  cp_all_low: cover property (@(posedge clk) (or_out == '0));

endmodule

// Example bind (connect clk from your environment):
// bind XC2COrArray xc2c_or_array_sva #(.W(56), .N(16))
//   u_xc2c_or_array_sva ( .clk(tb_clk), .pterms_in(pterms_in),
//                         .config_bits(config_bits), .or_out(or_out) );