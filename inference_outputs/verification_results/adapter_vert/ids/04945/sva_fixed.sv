module Span12Mux_s5_v_sva (
    input logic I,
    input logic O,
    input logic b0,
    input logic b000000000001,
    input logic b000000000010,
    input logic b000000000100,
    input logic b000000001000,
    input logic b000000010000,
    input logic b000000100000,
    input logic b000001000000,
    input logic b000010000000,
    input logic b000100000000,
    input logic b001000000000,
    input logic b010000000000,
    input logic b1,
    input logic b100000000000,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000000000001) |-> (O) == 1'b1 ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (I) == (12'b000000000010) |-> (O) == 1'b0 ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_1) (I) == (12'b000000000100) |-> (O) == 1'b1 ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_1) (I) == (12'b000000001000) |-> (O) == 1'b0 ; endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk_in_1) (I) == (12'b000000010000) |-> (O) == 1'b1 ; endproperty
assert property (ClockSynceotid_5);

property ClockSynceotid_6; @(posedge clk_in_1) (I) == (12'b000000100000) |-> (O) == 1'b0 ; endproperty
assert property (ClockSynceotid_6);

property ClockSynceotid_7; @(posedge clk_in_1) (I) == (12'b000001000000) |-> (O) == 1'b1 ; endproperty
assert property (ClockSynceotid_7);

property ClockSynceotid_8; @(posedge clk_in_1) (I) == (12'b000010000000) |-> (O) == 1'b0 ; endproperty
assert property (ClockSynceotid_8);

property ClockSynceotid_9; @(posedge clk_in_1) (I) == (12'b000100000000) |-> (O) == 1'b1 ; endproperty
assert property (ClockSynceotid_9);

property ClockSynceotid_10; @(posedge clk_in_1) (I) == (12'b001000000000) |-> (O) == 1'b0 ; endproperty
assert property (ClockSynceotid_10);

property ClockSynceotid_11; @(posedge clk_in_1) (I) == (12'b010000000000) |-> (O) == 1'b1 ; endproperty
assert property (ClockSynceotid_11);

property ClockSynceotid_12; @(posedge clk_in_1) (I) == (12'b100000000000) |-> (O) == 1'b0 ; endproperty
assert property (ClockSynceotid_12);

property ClockSynceotid_13; @(posedge clk_in_1) (I) != 12'b000000000001 && @(posedge clk_in_1) (I) != 12'b000000000010 && @(posedge clk_in_1) (I) != 12'b000000000100 && @(posedge clk_in_1) (I) != 12'b000000001000 && @(posedge clk_in_1) (I) != 12'b000000010000 && @(posedge clk_in_1) (I) != 12'b000000100000 && @(posedge clk_in_1) (I) != 12'b000001000000 && @(posedge clk_in_1) (I) != 12'b000010000000 && @(posedge clk_in_1) (I) != 12'b000100000000 && @(posedge clk_in_1) (I) != 12'b001000000000 && @(posedge clk_in_1) (I) != 12'b010000000000 && @(posedge clk_in_1) (I) != 12'b100000000000 |-> (O) == 1'b0 ; endproperty
assert property (ClockSynceotid_13);

endmodule