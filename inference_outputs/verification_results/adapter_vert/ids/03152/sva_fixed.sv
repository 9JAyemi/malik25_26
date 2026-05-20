module nand2_en_sva (
    input logic A,
    input logic B,
    input logic EN,
    input logic Z,
    input logic and_out,
    input logic nand1_out,
    input logic nand2_out,
    input logic clk_enable_19
);

property SafeStarteotid; @(posedge clk_enable_19) (A) |-> (nand1_out) ;endproperty
assert property (SafeStarteotid);

property SafeStarteotid_2; @(posedge clk_enable_19) (A) &&  (B) &&  (EN) |-> (nand2_out) ;endproperty
assert property (SafeStarteotid_2);

property ValidInputeotid; @(posedge clk_enable_19) (A) &&  (B) &&  (EN) |-> (and_out) ;endproperty
assert property (ValidInputeotid);

property ValidSynceotid; @(posedge clk_enable_19) (A) &&  (B) &&  (EN) &&  (nand2_out) &&  (and_out) |-> (Z) ;endproperty
assert property (ValidSynceotid);

endmodule