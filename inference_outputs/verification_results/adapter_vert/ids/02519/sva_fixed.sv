module addsub_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Q,
    input logic b1,
    input logic clk_in_15
);

property AddSynceotid; @(posedge clk_in_15) (C) == (1'b1) |-> (Q) == (A - B) ; endproperty
assert property (AddSynceotid);

property AddSynceotid_2; @(posedge clk_in_15) (C) != 1'b1  |-> (Q) == (A + B) ; endproperty
assert property (AddSynceotid_2);

endmodule