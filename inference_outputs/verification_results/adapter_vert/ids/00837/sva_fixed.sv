module wasca_hexdot_sva (
    input logic address,
    input logic chipselect,
    input logic clk,
    input logic data_out,
    input logic readdata,
    input logic reset_n,
    input logic write_n,
    input logic writedata
);

property ResetSynceotid; @(posedge clk) (reset_n) |-> data_out == 0 ;endproperty
assert property (ResetSynceotid);

property WriteSynceotid; @(posedge clk) (chipselect) && ( !write_n ) && ( address == 0 ) |-> data_out == writedata ;endproperty
assert property (WriteSynceotid);

property ReadSynceotid; @(posedge clk) (chipselect) && ( write_n ) && ( address != 0 ) |-> readdata == data_out ;endproperty
assert property (ReadSynceotid);

endmodule