module mux_4to1_enable_sva (
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic EN,
    input logic SEL,
    input logic Y,
    input logic b0,
    input logic b00,
    input logic b01,
    input logic b1,
    input logic b10,
    input logic b11,
    input logic clk_enable_14
);

property EnableSynceotid; @(posedge clk_enable_14) (SEL) == (2'b00) |-> (Y) == (D0) ; endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_14) (SEL) == (2'b01) |-> (Y) == (D1) ; endproperty
assert property (EnableSynceotid_2);

property EnableSynceotid_3; @(posedge clk_enable_14) (SEL) == (2'b10) |-> (Y) == (D2) ; endproperty
assert property (EnableSynceotid_3);

property EnableSynceotid_4; @(posedge clk_enable_14) (SEL) == (2'b11) |-> (Y) == (D3) ; endproperty
assert property (EnableSynceotid_4);

property EnableSynceotid_5; @(posedge clk_enable_14) (EN) != 1'b1  |-> (Y) == 8'b0 ; endproperty
assert property (EnableSynceotid_5);

endmodule