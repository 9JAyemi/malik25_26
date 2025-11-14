module Convolutional_Encoder_Viterbi_Decoder #(
  parameter k = 1, // number of input bits in each group
  parameter n = 2, // number of output bits in each group
  parameter p = 2, // number of bits in the encoder's shift register
  parameter m = 2 // number of bits in the decoder's shift register
)(
  input [k-1:0] in,
  output reg [n-1:0] enc_out,
  output reg [k-1:0] dec_out
);

reg [p-1:0] shift_reg; // encoder's shift register
reg [m-1:0] dec_reg; // decoder's shift register

// Encoder mapping function
function [n-1:0] encode;
  input [k-1:0] data;
  begin
    case (data)
      0: encode = {1'b1, 1'b0};
      1: encode = {1'b0, 1'b1};
      2: encode = {1'b1, 1'b1};
      3: encode = {1'b0, 1'b0};
    endcase
  end
endfunction

// Decoder decoding algorithm
function [k-1:0] decode;
  input [n-1:0] data;
  begin
    if (data == {1'b1, 1'b0}) decode = 1'b0;
    else if (data == {1'b0, 1'b1}) decode = 1'b1;
    else if (data == {1'b1, 1'b1}) decode = 2'b10;
    else if (data == {1'b0, 1'b0}) decode = 2'b11;
  end
endfunction

// Encoder process
always @(in) begin
  shift_reg = {in, shift_reg[p-1:1]}; // shift in new input bit
  enc_out = encode(shift_reg); // encode input data
end

// Decoder process
always @(enc_out) begin
  dec_reg = {enc_out, dec_reg[m-1:1]}; // shift in new encoded bit
  dec_out = decode(dec_reg); // decode encoded data
end

endmodule