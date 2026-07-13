module mem_enc_dec (
  input [mem_width-1:0] mem_addr,
  input [mem_width-1:0] mem_data,
  input [key_width-1:0] key,
  output [mem_width-1:0] enc_data
);

parameter mem_width = 8; // width of memory data
parameter key_width = 8; // width of encryption or decryption key

assign enc_data = mem_data ^ key;

endmodule