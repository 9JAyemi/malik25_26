module and_gate_extra_sva (
    input logic A,
    input logic B,
    input logic Y,
    input logic not_C,
    input logic clk_in_15
);

property ValidOnRiseeotid; @(posedge clk_in_15) (A) && (B) &&  (not_C) |-> (Y) ;endproperty
assert property (ValidOnRiseeotid);

property ValidOnRiseeotid_2; @(posedge clk_in_15) (A) && (B) &&  (not_C) ;endproperty
assert property (ValidOnRiseeotid_2);

property ValidOnRiseeotid_3; @(posedge clk_in_15) (A) && (B) &&  (not_C) ;endproperty
assert property (ValidOnRiseeotid_3);

endmodule