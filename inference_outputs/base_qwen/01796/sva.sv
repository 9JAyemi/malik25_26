```systemverilog
module mem_encrypt_decrypt_sva (
  input logic clk,
  input logic reset,
  input logic [7:0] data_in,
  input logic [7:0] key,
  input logic enable,
  output logic [7:0] data_out
);

  // At reset, data_out and encrypted_data should be 0
  reset: assert property (
    @(posedge clk) disable iff (!reset) (reset |-> (data_out == 8'b0) && (encrypted_data == 8'b0))
  );

  // When enable is high, data_out should be the result of data_in XOR key
  encrypt: assert property (
    @(posedge clk) disable iff (!reset) (enable |-> (data_out == (data_in ^ key)))
  );

  // When enable is low, data_out should be the same as data_in
  decrypt: assert property (
    @(posedge clk) disable iff (!reset) (!enable |-> (data_out == data_in))
  );

endmodule
```