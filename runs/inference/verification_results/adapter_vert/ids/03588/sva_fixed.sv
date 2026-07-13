module bitwise_and_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic and_result,
    input logic and0,
    input logic and1,
    input logic and2,
    input logic and3,
    input logic and4,
    input logic and5,
    input logic and6,
    input logic and7,
    input logic clk_in_1
);

property BitwiseAndeotid; @(posedge clk_in_1) (A) && (B) |-> (C) == (and_result); endproperty
assert property (BitwiseAndeotid);

property SyncAndeotid; @(posedge clk_in_1) (A) || (B) && !(C) |-> and0; endproperty
assert property (SyncAndeotid);

property SyncAndeotid_2; @(posedge clk_in_1) (A) || (B) && !(C) |-> and1; endproperty
assert property (SyncAndeotid_2);

property SyncAndeotid_3; @(posedge clk_in_1) (A) || (B) && !(C) |-> and2; endproperty
assert property (SyncAndeotid_3);

property SyncAndeotid_4; @(posedge clk_in_1) (A) || (B) && !(C) |-> and3; endproperty
assert property (SyncAndeotid_4);

property SyncAndeotid_5; @(posedge clk_in_1) (A) || (B) && !(C) |-> and4; endproperty
assert property (SyncAndeotid_5);

property SyncAndeotid_6; @(posedge clk_in_1) (A) || (B) && !(C) |-> and5; endproperty
assert property (SyncAndeotid_6);

property SyncAndeotid_7; @(posedge clk_in_1) (A) || (B) && !(C) |-> and6; endproperty
assert property (SyncAndeotid_7);

property SyncAndeotid_8; @(posedge clk_in_1) (A) || (B) && !(C) |-> and7; endproperty
assert property (SyncAndeotid_8);

endmodule