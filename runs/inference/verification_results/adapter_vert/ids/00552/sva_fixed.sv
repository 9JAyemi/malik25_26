module karnaugh_map_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic F,
    input logic m0,
    input logic clk_reset_19,
    input logic m1,
    input logic m2,
    input logic m3
);

property ResetSynceotid; @(negedge clk_reset_19) (A) && (B) && (C) |-> (F) == (m0) ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (A) && (B) && (!C) |-> (F) == (m1) ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (A) && (!B) && (C) |-> (F) == (m2) ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_19) (A) && (!B) && (!C) |-> (F) == (m3) ; endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk_reset_19) (A) && (B) && (C) || (A) && (B) && (!C) || (A) && (!B) && (C) || (A) && (!B) && (!C) |-> (F) == (m0) || (F) == (m1) || (F) == (m2) || (F) == (m3) ; endproperty
assert property (ResetSynceotid_5);

endmodule