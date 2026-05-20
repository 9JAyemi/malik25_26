module d_flip_flop_mux_sva (
    input logic clk,
    input logic d1,
    input logic d2,
    input logic q_reg,
    input logic sel,
    input logic data_15,
    input logic reg_1
);

property ClockSynceotid; @(negedge clk) (sel) |-> q_reg == d2 ; endproperty
assert property (ClockSynceotid);

property DataSynceotid; @(negedge clk) (sel) |-> data_15 == reg_1 ; endproperty
assert property (DataSynceotid);

property DataSynceotid_2; @(negedge clk) ! (sel) |-> q_reg == d1 ; endproperty
assert property (DataSynceotid_2);

property SyncDataeotid; @(negedge clk) ! (sel) |-> data_15 == reg_1 ; endproperty
assert property (SyncDataeotid);

endmodule