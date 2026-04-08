
module abs_difference_sum (
  input [15:0] input_a,
  input [15:0] input_b,
  output [15:0] output_sum
);

  wire [3:0] a_0to3, a_4to7, a_8to11, a_12to15;
  wire [3:0] b_0to3, b_4to7, b_8to11, b_12to15;
  wire [3:0] abs_diff_0to3, abs_diff_4to7, abs_diff_8to11, abs_diff_12to15;
  wire [15:0] abs_diff_sum;

  // Split input vectors into 4-bit vectors
  assign a_0to3 = input_a[3:0];
  assign a_4to7 = input_a[7:4];
  assign a_8to11 = input_a[11:8];
  assign a_12to15 = input_a[15:12];
  assign b_0to3 = input_b[3:0];
  assign b_4to7 = input_b[7:4];
  assign b_8to11 = input_b[11:8];
  assign b_12to15 = input_b[15:12];

  // Calculate absolute difference between each corresponding 4-bit vector
  assign abs_diff_0to3 = (a_0to3 > b_0to3) ? (a_0to3 - b_0to3) : (b_0to3 - a_0to3);
  assign abs_diff_4to7 = (a_4to7 > b_4to7) ? (a_4to7 - b_4to7) : (b_4to7 - a_4to7);
  assign abs_diff_8to11 = (a_8to11 > b_8to11) ? (a_8to11 - b_8to11) : (b_8to11 - a_8to11);
  assign abs_diff_12to15 = (a_12to15 > b_12to15) ? (a_12to15 - b_12to15) : (b_12to15 - a_12to15);

  // Calculate sum of absolute differences
  assign abs_diff_sum = {abs_diff_12to15, abs_diff_8to11, abs_diff_4to7, abs_diff_0to3};
  assign output_sum = abs_diff_sum;

endmodule
