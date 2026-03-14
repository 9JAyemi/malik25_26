module exu_eclcomp8 (
  input [7:0] a,
  input [7:0] b,
  output result
);

  wire [7:0] xor_result;
  wire [3:0] first_nor_input;
  wire [3:0] second_nor_input;
  wire [2:0] third_nor_input;
  wire [2:0] nand_input;
  
  assign xor_result = a ^ b;
  assign first_nor_input = {~xor_result[7], ~xor_result[6], ~xor_result[5], ~xor_result[4]};
  assign second_nor_input = {~xor_result[3], ~xor_result[2], ~xor_result[1], ~xor_result[0]};
  assign third_nor_input = {~xor_result[4], ~xor_result[5], ~xor_result[6]};
  assign nand_input = {~second_nor_input[3], ~second_nor_input[2], ~second_nor_input[1], ~third_nor_input[2]};
  
  assign result = ~(|(first_nor_input) | |(second_nor_input) | ~(|(third_nor_input) | &(nand_input)));

endmodule