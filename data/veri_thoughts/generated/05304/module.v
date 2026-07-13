
module nor_4bit (
  input [3:0] A,
  input [3:0] B,
  output [3:0] Z
);

  wire [3:0] nor_result;

  nor nor0(nor_result[0], A[0], B[0]);
  nor nor1(nor_result[1], A[1], B[1]);
  nor nor2(nor_result[2], A[2], B[2]);
  nor nor3(nor_result[3], A[3], B[3]);

  assign Z = nor_result;

endmodule
