module mux_2to1_enable_sva (
    input logic A,
    input logic B,
    input logic EN,
    input logic Y,
    input logic b1,
    input logic clk_enable_19
);

property EnableSynceotid; @(posedge clk_enable_19) (EN) |-> (Y) == (A) ; endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_19) (EN) != 1'b1  &&  (A) != (B) |-> (Y) == (B) ; endproperty
assert property (EnableSynceotid_2);

endmodule