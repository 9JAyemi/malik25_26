module r_FAULT_STATUS_sva (
    input logic clk,
    input logic in_data,
    input logic reg_0x1F,
    input logic reset,
    input logic wenb,
    input logic h00
);

property ResetSynceotid; @(posedge clk) (reset) |-> reg_0x1F == 8'h00 ;endproperty
assert property (ResetSynceotid);

property WriteSynceotid; @(posedge clk) ( !reset ) &&  (  wenb ) |-> reg_0x1F == reg_0x1F ;endproperty
assert property (WriteSynceotid);

property WriteSynceotid_2; @(posedge clk) ( !reset ) &&  (  !wenb ) |-> reg_0x1F == in_data ;endproperty
assert property (WriteSynceotid_2);

endmodule