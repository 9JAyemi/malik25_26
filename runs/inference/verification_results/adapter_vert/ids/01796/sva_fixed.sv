module mem_encrypt_decrypt_sva (
    input logic clk,
    input logic data_in,
    input logic data_out,
    input logic enable,
    input logic encrypted_data,
    input logic reset,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (reset) |-> data_out == 8'b0 && encrypted_data == 8'b0 ;endproperty
assert property (ResetSynceotid);

property ValidDataeotid; @(posedge clk) (reset) != 1'b1 &&  (enable) |-> data_out == encrypted_data ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk) (reset) != 1'b1 &&  !(enable)  |-> data_out == data_in ;endproperty
assert property (ValidDataeotid_2);

endmodule