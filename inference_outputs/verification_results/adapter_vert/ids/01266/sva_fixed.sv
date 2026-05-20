module AND4_sva (
    input logic A,
    input logic AB,
    input logic B,
    input logic C,
    input logic D,
    input logic Z,
    input logic ABCD,
    input logic CD,
    input logic b1,
    input logic clk_in_1
);

property SyncAndeotid; @(posedge clk_in_1) (A) and (B) |-> (AB); endproperty
assert property (SyncAndeotid);

property SyncAndeotid_2; @(posedge clk_in_1) (C) and (D) |-> (CD); endproperty
assert property (SyncAndeotid_2);

property ValidDataeotid; @(posedge clk_in_1) (AB) and (CD) |-> (ABCD); endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (A) and (B) and (C) and (D) == 1'b1 |-> (Z) == 1'b1 ; endproperty
assert property (ValidDataeotid_2);

endmodule