module four_bit_adder_sva (
    input logic A,
    input logic B,
    input logic Ci,
    input logic Co,
    input logic S,
    input logic n1,
    input logic bxxxx,
    input logic clk_in_1,
    input logic n7
);

property AdderSynceotid; @(posedge clk_in_1) ( A ) |-> ( n1 ) ; endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) ( B ) |-> ( n1 ) ; endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_1) ( Ci ) |-> ( n1 ) ; endproperty
assert property (AdderSynceotid_3);

property AdderSynceotid_4; @(posedge clk_in_1) ( n1 ) == ( 4'bxxxx ) |-> ( S ) == ( n1 ) ; endproperty
assert property (AdderSynceotid_4);

property AdderSynceotid_5; @(posedge clk_in_1) ( n1 ) == ( 4'bxxxx ) |-> ( Co ) == ( n7 ) ; endproperty
assert property (AdderSynceotid_5);

endmodule