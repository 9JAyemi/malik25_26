module shift_register_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic reg_data
);

property ClockSynceotid; @(posedge clk) ( d ) |-> reg_data == {reg_data[1:0], d} ;endproperty
assert property (ClockSynceotid);

property SyncRsteotid; @(posedge clk) ( d ) |-> q == reg_data[0] ;endproperty
assert property (SyncRsteotid);

endmodule