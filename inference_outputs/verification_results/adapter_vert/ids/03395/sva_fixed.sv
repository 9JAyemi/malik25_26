module AND3_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Z,
    input logic clk_in_1
);

property AND3eotid; @(posedge clk_in_1) ( A ) && ( B ) && ( C ) |-> ( Z ) ;endproperty
assert property (AND3eotid);

property ValidOnRiseeotid; @(posedge clk_in_1) ( A ) && ( B ) && ( C ) |-> ( Z ) ;endproperty
assert property (ValidOnRiseeotid);

property ValidOnRiseeotid_2; @(posedge clk_in_1) ( A ) && ( B ) && ( C ) |-> ( Z ) ;endproperty
assert property (ValidOnRiseeotid_2);

endmodule