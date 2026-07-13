module or4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic or_output,
    input logic clk_in_11
);

property ORSynceotid; @(posedge clk_in_11) (A) |-> (X) ; endproperty
assert property (ORSynceotid);

property ORSynceotid_2; @(posedge clk_in_11) (B) |-> (X) ; endproperty
assert property (ORSynceotid_2);

property ORSynceotid_3; @(posedge clk_in_11) (C) |-> (X) ; endproperty
assert property (ORSynceotid_3);

property ORSynceotid_4; @(posedge clk_in_11) (D) |-> (X) ; endproperty
assert property (ORSynceotid_4);

property ORSynceotid_5; @(posedge clk_in_11) (A) |-> (or_output) ; endproperty
assert property (ORSynceotid_5);

property ORSynceotid_6; @(posedge clk_in_11) (B) |-> (or_output) ; endproperty
assert property (ORSynceotid_6);

property ORSynceotid_7; @(posedge clk_in_11) (C) |-> (or_output) ; endproperty
assert property (ORSynceotid_7);

property ORSynceotid_8; @(posedge clk_in_11) (D) |-> (or_output) ; endproperty
assert property (ORSynceotid_8);

endmodule