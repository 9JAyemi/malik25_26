module two_bit_comparator_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic clk_in_1
);

property SyncEqeotid; @(posedge clk_in_1) (A) == (B) |-> (C) == 2'b00 ; endproperty
assert property (SyncEqeotid);

property SyncGoeotid; @(posedge clk_in_1) (A) != (B) && (A) > (B) |-> (C) == 2'b01 ; endproperty
assert property (SyncGoeotid);

property SyncLoadeotid; @(posedge clk_in_1) (A) != (B) && !(A) > (B)  |-> (C) == 2'b10; endproperty
assert property (SyncLoadeotid);

endmodule