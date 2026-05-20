module DFFE_sva (
    input logic D,
    input logic EN,
    input logic Q,
    input logic ENCLK,
    input logic TE,
    input logic b0,
    input logic b1,
    input logic clk_enable_19
);

property EnableSynceotid; @(posedge clk_enable_19) (EN) |-> (Q) == (D) ;endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_19) (EN) &&  (TE) |-> (Q) == (D) ;endproperty
assert property (EnableSynceotid_2);

property EnableSynceotid_3; @(posedge clk_enable_19) (EN) &&  (TE) |-> (ENCLK) == (1'b1) ;endproperty
assert property (EnableSynceotid_3);

property EnableSynceotid_4; @(posedge clk_enable_19) (EN) &&  ( !  TE ) |-> (ENCLK) == (1'b0) ;endproperty
assert property (EnableSynceotid_4);

endmodule