// SVA for TwosComplement
// Checks functional correctness, X-propagation, and covers all 16 input-output mappings.

module TwosComplement_sva (
  input logic        clk,
  input logic [3:0]  in,
  input logic [3:0]  out
);

  // establish one-cycle history validity
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid)

  // No X/Z on sampled signals
  a_no_x: assert property (!$isunknown({in,out}));

  // Functional check: out equals two's complement of prior-cycle in
  a_twos: assert property (out == (~$past(in) + 4'd1));

  // Equivalent arithmetic check: out + prior in == 0 mod 16 (LSBs zero)
  a_sum_zero: assert property (((out + $past(in))[3:0]) == 4'd0);

  // Full functional coverage: observe every input value and its mapped output
  genvar v;
  for (v = 0; v < 16; v++) begin : gen_cov_all_pairs
    localparam logic [3:0] VAL = v[3:0];
    c_pair: cover property ($past(in) == VAL && out == (~VAL + 4'd1));
  end

endmodule

bind TwosComplement TwosComplement_sva sva_i (.clk(clk), .in(in), .out(out));