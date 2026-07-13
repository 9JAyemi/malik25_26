module ripple_adder_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic Cout,
    input logic S,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (B) |-> (S) ;endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_1) (Cin) |-> (S) ;endproperty
assert property (AdderSynceotid_3);

property AdderSynceotid_4; @(posedge clk_in_1) (A) && (B) && (Cin) |-> (Cout) ;endproperty
assert property (AdderSynceotid_4);

property AdderSynceotid_5; @(posedge clk_in_1) (A) && (B) && ! (Cin) |-> ! (Cout) ;endproperty
assert property (AdderSynceotid_5);

property AdderSynceotid_6; @(posedge clk_in_1) (A) && ! (B) && (Cin) |-> ! (Cout) ;endproperty
assert property (AdderSynceotid_6);

property AdderSynceotid_7; @(posedge clk_in_1) ! (A) && (B) && (Cin) |-> ! (Cout) ;endproperty
assert property (AdderSynceotid_7);

endmodule