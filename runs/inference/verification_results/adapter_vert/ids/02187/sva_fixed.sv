module data_storage_sva (
    input logic clk,
    input logic in_data,
    input logic in_valid,
    input logic out_data,
    input logic out_valid,
    input logic reset,
    input logic stored_data,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (reset) |-> stored_data == 0 && out_valid == 0 ;endproperty
assert property (ResetSynceotid);

property ValidDataeotid; @(posedge clk) (reset) != 1'b1 &&  (in_valid) |-> stored_data == in_data && out_valid == 1 ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk) (reset) != 1'b1 &&  !(in_valid)  |-> out_valid == 0 ;endproperty
assert property (ValidDataeotid_2);

property SyncDataeotid; @(posedge clk) (reset) != 1'b1  |-> out_data == stored_data; endproperty
assert property (SyncDataeotid);

endmodule