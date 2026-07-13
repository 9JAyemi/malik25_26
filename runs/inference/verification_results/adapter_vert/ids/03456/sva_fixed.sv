module shift_register_4bit_sva (
    input logic clk,
    input logic in,
    input logic load,
    input logic ser_out_reg,
    input logic shift_reg
);

property LoadSynceotid; @(posedge clk) (load) |-> shift_reg == in ;endproperty
assert property (LoadSynceotid);

property ShiftOneotid; @(posedge clk) ( !load )  |-> shift_reg == {shift_reg[2:0], shift_reg[3]} ;endproperty
assert property (ShiftOneotid);

property SyncOuteotid; @(posedge clk) ( !load )  |-> ser_out_reg == shift_reg[3] ;endproperty
assert property (SyncOuteotid);

endmodule