module four_input_and_sva (
    input logic A,
    input logic AB,
    input logic ABCD,
    input logic B,
    input logic C,
    input logic CD,
    input logic D,
    input logic X,
    input logic clk_in_14
);

property SyncIneotid; @(posedge clk_in_14) (A) && (B) |-> (AB); endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_14) (C) && (D) |-> (CD); endproperty
assert property (SyncIneotid_2);

property ValidSynceotid; @(posedge clk_in_14) (AB) && (CD) |-> (ABCD); endproperty
assert property (ValidSynceotid);

property ValidSynceotid_2; @(posedge clk_in_14) (ABCD) |-> ! (X); endproperty
assert property (ValidSynceotid_2);

endmodule