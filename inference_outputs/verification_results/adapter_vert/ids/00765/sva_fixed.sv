module mux_4to1_sva (
    input logic enable,
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
    input logic clk_enable_16
);

property EnableSynceotid; @(posedge clk_enable_16) (sel) == (2'b00) &&  (enable) |-> (out) == (in0) ;endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_16) (sel) == (2'b01) &&  (enable) |-> (out) == (in1) ;endproperty
assert property (EnableSynceotid_2);

property EnableSynceotid_3; @(posedge clk_enable_16) (sel) == (2'b10) &&  (enable) |-> (out) == (in2) ;endproperty
assert property (EnableSynceotid_3);

property ValidDataeotid; @(posedge clk_enable_16) (sel) == (2'b11) &&  (enable) |-> (out) == (in3) ;endproperty
assert property (ValidDataeotid);

endmodule