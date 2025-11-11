
module hyperbolic (
  input x,
  output sineh_out,
  output cosh_out,
  output tanh_out
);

  wire signed [31:0] exp_x;
  wire signed [31:0] exp_neg_x;
  wire signed [31:0] exp_x_plus_exp_neg_x;
  wire signed [31:0] sineh;
  wire signed [31:0] cosh;

  assign exp_x = $signed({{20{1'b0}}, x});
  assign exp_neg_x = $signed({{20{1'b0}}, -x});
  assign exp_x_plus_exp_neg_x = exp_x + exp_neg_x;

  assign sineh = exp_x - exp_neg_x;
  assign cosh = exp_x_plus_exp_neg_x >> 1;

  assign sineh_out = sineh >> 1;
  assign cosh_out = cosh >> 1;
  assign tanh_out = sineh / cosh;

endmodule
