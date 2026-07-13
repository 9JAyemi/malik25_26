module binary_multiplier_sva (
    input logic a,
    input logic out,
    input logic temp_out,
    input logic clk_in_14
);

property ValidOnRiseeotid; @(posedge clk_in_14) (a) |-> (temp_out) ;endproperty
assert property (ValidOnRiseeotid);

property ValidOnRiseeotid_2; @(posedge clk_in_14) (a) |-> (out) ;endproperty
assert property (ValidOnRiseeotid_2);

endmodule