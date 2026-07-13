module mem_enc_dec_sva (
  input logic clk,
  input logic [mem_width-1:0] mem_addr,
  input logic [mem_width-1:0] mem_data,
  input logic [key_width-1:0] key,
  output logic [mem_width-1:0] enc_data
);

parameter mem_width = 8; // width of memory data
parameter key_width = 8; // width of encryption or decryption key

  // Combinational logic: enc_data is the result of mem_data XOR key
  // This logic is always active, so we use @(posedge clk) to ensure proper clocking
  combinational_logic: assert property (
    @(posedge clk) enc_data == (mem_data ^ key)
  ) else $error("Combinational logic error: enc_data is not equal to mem_data XOR key");

endmodule