module main(
  input [2:0] A1,
  input [2:0] A2,
  input [2:0] A3,
  output Y
);

wire a1_and, a2_and, a3_and; 

assign a1_and = &A1;
assign a2_and = &A2;
assign a3_and = &A3;

assign Y = a1_and | a2_and | a3_and; 

endmodule