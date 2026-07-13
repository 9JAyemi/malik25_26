module up_down_counter_sva (
    input logic Q,
    input logic clk,
    input logic input_data,
    input logic load,
    input logic up_down,
    input logic b1
);

property LoadSynceotid; @(posedge clk) (load) |-> Q == input_data ; endproperty
assert property (LoadSynceotid);

property ClockSynceotid; @(posedge clk) (load) != 1'b1  &&  (up_down) |-> Q == (Q + 1) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (load) != 1'b1  &&  !(up_down)  |-> Q == (Q - 1) ; endproperty
assert property (ClockSynceotid_2);

endmodule