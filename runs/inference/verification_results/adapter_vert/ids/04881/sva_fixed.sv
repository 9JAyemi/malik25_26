module up_down_counter_4bit_sva (
    input logic Down,
    input logic Q,
    input logic Up,
    input logic clk,
    input logic b0000,
    input logic b1111
);

property ClockSynceotid; @(posedge clk) (Up) |-> (Q != 4'b1111) |-> Q == (Q + 1); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (Down) |-> (Q != 4'b0000) |-> Q == (Q - 1); endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk) (Up) &&  (Q == 4'b1111) |-> Q == 4'b0000; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk) (Down) &&  (Q == 4'b0000) |-> Q == 4'b1111; endproperty
assert property (ClockSynceotid_4);

endmodule