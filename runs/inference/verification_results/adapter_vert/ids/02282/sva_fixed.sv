module shift_register_sva (
    input logic clk,
    input logic data_in,
    input logic data_out,
    input logic load,
    input logic shift_right,
    input logic stage1,
    input logic stage2,
    input logic stage3,
    input logic stage4
);

property LoadSynceotid; @(posedge clk) (load) |-> stage1 == data_in && stage2 == stage1 && stage3 == stage2 && stage4 == stage3 ;endproperty
assert property (LoadSynceotid);

property ShiftRighteotid; @(posedge clk) ( !load ) &&  ( shift_right ) |-> stage1 == stage4 && stage2 == stage1 && stage3 == stage2 ;endproperty
assert property (ShiftRighteotid);

property ShiftIneotid; @(posedge clk) ( !load ) &&  ( !shift_right ) |-> stage1 == stage2 && stage2 == stage3 && stage3 == stage4 ;endproperty
assert property (ShiftIneotid);

property DataSynceotid; @(posedge clk) ( !load ) &&  ( !shift_right ) |-> data_out == stage4 ;endproperty
assert property (DataSynceotid);

endmodule