module mux_4to1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic SEL,
    input logic Y,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (SEL) == (2'b00) |-> (Y) == (A) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (SEL) == (2'b01) |-> (Y) == (B) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_1) (SEL) == (2'b10) |-> (Y) == (C) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_1) (SEL) == (2'b11) |-> (Y) == (D) ; endproperty
assert property (ClockSynceotid_4);

endmodule