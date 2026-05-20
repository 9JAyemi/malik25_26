module up_down_counter_sva (
    input logic clk,
    input logic load,
    input logic out,
    input logic up_down,
    input logic b000,
    input logic b1,
    input logic data_14,
    input logic data_15
);

property ResetOnLoadSynceotid; @(posedge clk) (load) |-> out == 3'b000 ; endproperty
assert property (ResetOnLoadSynceotid);

property ClockSynceotid; @(posedge clk) (load) != 1'b1 &&  (up_down) |-> out == data_15 ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (load) != 1'b1 &&  !(up_down)  |-> out == data_14 ; endproperty
assert property (ClockSynceotid_2);

endmodule