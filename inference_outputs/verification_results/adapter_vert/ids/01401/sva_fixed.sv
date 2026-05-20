module shift_register_sva (
    input logic clk,
    input logic data_in,
    input logic data_out,
    input logic load,
    input logic shift_reg,
    input logic b1
);

property LoadSynceotid; @(posedge clk) (load) |-> shift_reg == data_in ;endproperty
assert property (LoadSynceotid);

property ShiftSynceotid; @(posedge clk) (load) != 1'b1  |-> shift_reg == data_out ;endproperty
assert property (ShiftSynceotid);

endmodule