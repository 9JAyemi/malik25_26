module absolute_value_calculator #(
  parameter n = 8
) (
  input signed [n-1:0] num,
  output [n-1:0] abs_num
);

assign abs_num = (num[n-1] == 1) ? (~num + 1) : num;

endmodule