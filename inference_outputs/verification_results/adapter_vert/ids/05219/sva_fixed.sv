module xor_gate_sva (
    input logic A,
    input logic B,
    input logic X,
    input logic not_A,
    input logic not_B,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (A) |-> not_A ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (B) |-> not_B ; endproperty
assert property (ClockSynceotid_2);

property ValidXorOuteotid; @(posedge clk_in_1) (A) &&  ( not_B ) |->  (X) ; endproperty
assert property (ValidXorOuteotid);

property ValidXorOuteotid_2; @(posedge clk_in_1) (not_A) &&  ( B ) |->  (X) ; endproperty
assert property (ValidXorOuteotid_2);

endmodule