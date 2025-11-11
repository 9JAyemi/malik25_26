module compression_decompression (
  input [7:0] data_in,
  output [3:0] data_out
);

  wire [1:0] code;
  assign code = (data_in[7:4] == 4'b0000) ? 2'b10 : 
                (data_in[7:4] == 4'b1111) ? 2'b11 :
                (data_in[7:4] == data_in[3:0]) ? 2'b01 : 
                2'b00;

  assign data_out = {code, (code == 2'b10 || code == 2'b11) ? data_in[7:6] : data_in[1:0]};

endmodule
