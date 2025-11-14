
module addsub(A, B, subtract, result);

  input [3:0] A;
  input [3:0] B;
  input subtract;
  output [3:0] result;

  wire [3:0] B_neg;
  wire [3:0] temp_result;

  assign B_neg = ~B + 1; // Two's complement of B

  assign temp_result = A + (subtract ? B_neg : B);

  assign result = temp_result + (subtract ? B_neg : B);

endmodule