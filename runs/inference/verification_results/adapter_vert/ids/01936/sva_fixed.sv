module xor_shift_register_sva (
    input logic clk,
    input logic data,
    input logic ena,
    input logic load,
    input logic out_if_else,
    input logic q,
    input logic shift_reg,
    input logic b0,
    input logic b00
);

property LoadSynceotid; @(posedge clk) (load) |-> shift_reg == data ;endproperty
assert property (LoadSynceotid);

property ValidDataeotid; @(posedge clk) ( !load ) &&  (  ena != 2'b00 ) |-> shift_reg == data ;endproperty
assert property (ValidDataeotid);

property SyncCheckeotid; @(posedge clk) ( !load )  &&  (  !(ena != 2'b00)  )  |-> out_if_else == 1'b0 ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) ( !load )  &&  (  !(ena != 2'b00)  )  |-> q == shift_reg ;endproperty
assert property (SyncCheckeotid_2);

endmodule