module mux_4to1_en_sva (
    input logic en,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_enable_19
);

property EnableSynceotid; @(posedge clk_enable_19) (sel) == (2'b00) |-> (out) == (en) && (out) == (in0) ; endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_19) (sel) == (2'b01) |-> (out) == (en) && (out) == (in1) ; endproperty
assert property (EnableSynceotid_2);

property EnableSynceotid_3; @(posedge clk_enable_19) (sel) == (2'b10) |-> (out) == (en) && (out) == (in2) ; endproperty
assert property (EnableSynceotid_3);

property EnableSynceotid_4; @(posedge clk_enable_19) (sel) == (2'b11) |-> (out) == (en) && (out) == (in3) ; endproperty
assert property (EnableSynceotid_4);

endmodule