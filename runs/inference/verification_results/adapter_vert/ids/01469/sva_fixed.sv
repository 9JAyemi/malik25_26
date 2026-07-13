module mux_sva (
    input logic ABCD,
    input logic EN,
    input logic SEL,
    input logic Y,
    input logic b0,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic bx,
    input logic clk_reset_14
);

property ResetSynceotid; @(negedge clk_reset_14) (EN) |-> (Y) == (1'b0) ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_14) (EN) &&  (  (SEL) == (2'b00)  ) |-> (Y) == (ABCD) ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_14) (EN) &&  (  (SEL) == (2'b01)  ) |-> (Y) == (ABCD) ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_14) (EN) &&  (  (SEL) == (2'b10)  ) |-> (Y) == (ABCD) ; endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk_reset_14) (EN) &&  (  (SEL) == (2'b11)  ) |-> (Y) == (ABCD) ; endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(negedge clk_reset_14) ! (EN)  |-> (Y) == (1'bx) ; endproperty
assert property (ResetSynceotid_6);

endmodule