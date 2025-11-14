module booth_encoder_5(
  input [2:0] B_in,
  output [2:0] A_out
);

assign A_out = (B_in[2] ^ B_in[1] ^ B_in[0]) ? 3'b001 : 
               (B_in[2] ^ B_in[0]) ? 3'b010 :
               (B_in[2] ^ B_in[1]) ? 3'b011 :
               (B_in[1] ^ B_in[0]) ? 3'b100 :
               (B_in[2]) ? 3'b101 :
               (B_in[1]) ? 3'b110 :
               (B_in[0]) ? 3'b111 :
               3'b000;

endmodule