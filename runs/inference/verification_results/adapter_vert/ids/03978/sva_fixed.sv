module decoder_2to4_with_enable_sva (
    input logic A,
    input logic B,
    input logic EN,
    input logic Y,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b01,
    input logic b0100,
    input logic b10,
    input logic b1000,
    input logic b11,
    input logic clk_enable_14
);

property EnableSynceotid; @(posedge clk_enable_14) (EN) |-> (Y) == (4'b0001) ; endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_14) (EN) &&  (  {A,B} == 2'b01  ) |-> (Y) == (4'b0010) ; endproperty
assert property (EnableSynceotid_2);

property EnableSynceotid_3; @(posedge clk_enable_14) (EN) &&  (  {A,B} == 2'b10  ) |-> (Y) == (4'b0100) ; endproperty
assert property (EnableSynceotid_3);

property ValidOnEnableeotid; @(posedge clk_enable_14) (EN) &&  (  {A,B} == 2'b11  ) |-> (Y) == (4'b1000) ; endproperty
assert property (ValidOnEnableeotid);

property EnableSynceotid_4; @(posedge clk_enable_14) ! (EN)  |-> (Y) == (4'b0000) ; endproperty
assert property (EnableSynceotid_4);

endmodule