module full_adder_sva (
    input logic A,
    input logic B,
    input logic Ci,
    input logic Co,
    input logic S,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) ( A ) != (  B ) |-> ( S ) != (  Ci ) ;endproperty
assert property (AdderSynceotid);

property ValidAddereotid; @(posedge clk_in_1) ( A ) != (  B ) &&  (  Ci ) |-> ( S ) != (  Ci ) ;endproperty
assert property (ValidAddereotid);

property CarrySynceotid; @(posedge clk_in_1) ( A ) == (  B ) &&  (  Ci ) |-> ( Co ) ;endproperty
assert property (CarrySynceotid);

property ValidAddereotid_2; @(posedge clk_in_1) ( A ) == (  B )  &&  (  Ci ) !=  (  S ) |-> ( Co ) ;endproperty
assert property (ValidAddereotid_2);

endmodule