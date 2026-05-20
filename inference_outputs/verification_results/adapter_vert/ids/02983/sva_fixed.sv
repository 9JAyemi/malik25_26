module adder_sva (
    input logic A,
    input logic B,
    input logic C_out,
    input logic S,
    input logic c,
    input logic b0,
    input logic b0000,
    input logic clk_in_19
);

property AdderSynceotid; @(posedge clk_in_19) (A) != (B) |-> (S) != (A); endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_19) (A) != (B) |-> (C_out) == (c); endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_19) (A) == (B) && (A) != 4'b0000 |-> (S) == 4'b0000 ; endproperty
assert property (AdderSynceotid_3);

property AdderSynceotid_4; @(posedge clk_in_19) (A) == (B) && (A) != 4'b0000 |-> (C_out) == 1'b0 ; endproperty
assert property (AdderSynceotid_4);

endmodule