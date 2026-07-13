module ripple_carry_adder_sva (
    input logic A,
    input logic B,
    input logic COUT,
    input logic CIN,
    input logic SUM,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (COUT) ; endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (B) |-> (COUT) ; endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (A) &&  (B)  &&  (CIN) |-> (COUT) ; endproperty
assert property (AddOneeotid_3);

property AddOneeotid_4; @(posedge clk_in_1) (A) &&  (B)  &&  (!CIN)  ||  (A) &&  (!B)  &&  (CIN)  ||  (!A) &&  (B)  &&  (CIN) |-> (SUM) ; endproperty
assert property (AddOneeotid_4);

endmodule