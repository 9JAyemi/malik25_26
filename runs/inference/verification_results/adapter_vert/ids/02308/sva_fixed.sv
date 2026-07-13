module nand2_module_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic out
);

property SyncNandCheckeotid; @(posedge clk) (in1) && (in2) |-> !out ;endproperty
assert property (SyncNandCheckeotid);

property SyncNandCheckeotid_2; @(posedge clk) (in1) && !(in2) |->  out ;endproperty
assert property (SyncNandCheckeotid_2);

property SyncNandCheckeotid_3; @(posedge clk) !(in1) && (in2) |->  out ;endproperty
assert property (SyncNandCheckeotid_3);

property SyncNandCheckeotid_4; @(posedge clk) !(in1) && !(in2) |->  out ;endproperty
assert property (SyncNandCheckeotid_4);

endmodule