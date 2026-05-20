module shift_register_sva (
    input logic clk,
    input logic data_in,
    input logic data_out,
    input logic load
);

property LoadSynceotid; @(posedge clk) (load) |-> data_out == data_in ; endproperty
assert property (LoadSynceotid);

property ShiftOneotid; @(posedge clk) ( !load )  |-> data_out == data_out ; endproperty
assert property (ShiftOneotid);

endmodule