module Multiplexer_sva (
    input logic D0,
    input logic D1,
    input logic S,
    input logic ctrl,
    input logic clk_in_14
);

property DataSynceotid; @(posedge clk_in_14) (ctrl) |-> (S) == (D1) ; endproperty
assert property (DataSynceotid);

property DataSynceotid_2; @(posedge clk_in_14) (ctrl) |-> (S) == (D0) ; endproperty
assert property (DataSynceotid_2);

endmodule