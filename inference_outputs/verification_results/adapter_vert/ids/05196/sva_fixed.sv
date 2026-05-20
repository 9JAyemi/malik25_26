module mux_4to1_sva (
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic EN,
    input logic SEL,
    input logic Y,
    input logic mux_2to1_out_2,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_12
);

property ClockSynceotid; @(posedge clk_in_12) (SEL) == (2'b00) |-> (Y) == (D0) ; endproperty
assert property (ClockSynceotid);

property ValidDataeotid; @(posedge clk_in_12) (SEL) == (2'b01) |-> (Y) == (D1) ; endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_12) (SEL) == (2'b10) |-> (Y) == (D2) ; endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_12) (SEL) == (2'b11) |-> (Y) == (D3) ; endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_12) (EN) |-> (Y) == (mux_2to1_out_2) ; endproperty
assert property (ValidDataeotid_4);

endmodule