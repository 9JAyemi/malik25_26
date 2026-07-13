module and3b_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic X,
    input logic b0,
    input logic b1,
    input logic bx,
    input logic clk_in_14
);

property ValidOnRiseeotid; @(posedge clk_in_14) (A_N) && (B) && (C) |-> (X) == 1'b1 ; endproperty
assert property (ValidOnRiseeotid);

property SafeStarteotid; @(posedge clk_in_14) (A_N) != 1'b0 &&  (B) != 1'b0 &&  (C) != 1'b0  |-> (X) == 1'b0; endproperty
assert property (SafeStarteotid);

property ValidSynceotid; @(posedge clk_in_14) (A_N) != 1'b1 ||  (B) != 1'b1 ||  (C) != 1'b1  |-> (X) == 1'bx; endproperty
assert property (ValidSynceotid);

endmodule