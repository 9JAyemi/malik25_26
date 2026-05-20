module Multiplexer_AC__parameterized36_sva (
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic S,
    input logic ctrl,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic bx,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (2'b00) |-> (S) == (D0) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_14) (ctrl) == (2'b01) |-> (S) == (D1) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_14) (ctrl) == (2'b10) |-> (S) == (D2) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_14) (ctrl) == (2'b11) |-> (S) == (D3) ; endproperty
assert property (ClockSynceotid_4);

property ValidCtrleotid; @(posedge clk_in_14) (ctrl) != 2'b00 && (ctrl) != 2'b01 && (ctrl) != 2'b10 && (ctrl) != 2'b11 |-> (S) == 1'bx ; endproperty
assert property (ValidCtrleotid);

endmodule