module mux_4to1_enable_sva (
    input logic en,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel,
    input logic b0,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_enable_13
);

property EnableSynceotid; @(posedge clk_enable_13) (sel) == (2'b00) &&  (en) |-> (out) == (in0) ; endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_13) (sel) == (2'b01) &&  (en) |-> (out) == (in1) ; endproperty
assert property (EnableSynceotid_2);

property EnableSynceotid_3; @(posedge clk_enable_13) (sel) == (2'b10) &&  (en) |-> (out) == (in2) ; endproperty
assert property (EnableSynceotid_3);

property EnableSynceotid_4; @(posedge clk_enable_13) (sel) == (2'b11) &&  (en) |-> (out) == (in3) ; endproperty
assert property (EnableSynceotid_4);

property ValidIneotid; @(posedge clk_enable_13) (sel) != 2'b00 && @(posedge clk_enable_13) (sel) != 2'b01 && @(posedge clk_enable_13) (sel) != 2'b10 && @(posedge clk_enable_13) (sel) != 2'b11  |-> (out) == 4'b0 ; endproperty
assert property (ValidIneotid);

endmodule