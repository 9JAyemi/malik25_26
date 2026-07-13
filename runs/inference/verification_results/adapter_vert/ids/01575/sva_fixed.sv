module parity_check_sva (
    input logic data,
    input logic parity_error,
    input logic xor_result,
    input logic b0xxxxxx,
    input logic clk_in_1
);

property DataSynceotid; @(posedge clk_in_1) (data) |-> (parity_error) == (xor_result == 1); endproperty
assert property (DataSynceotid);

property SyncCheckeotid; @(posedge clk_in_1) (data) |-> (xor_result) == (data); endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (data) |-> (parity_error) != 7'b0xxxxxx; endproperty
assert property (SyncCheckeotid_2);

endmodule