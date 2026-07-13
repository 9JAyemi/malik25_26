module top_module_sva (
    input logic A,
    input logic A_greater_B,
    input logic B,
    input logic result,
    input logic shift_amount,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (A) > (B) |-> (A_greater_B) ; endproperty
assert property (ClockSynceotid);

property ShiftOnClockeotid; @(posedge clk_in_15) (A) > (B) |-> (result) == (A << shift_amount) ; endproperty
assert property (ShiftOnClockeotid);

property SyncCheckeotid; @(posedge clk_in_15) (A) < (B)  |-> (result) == (B >> shift_amount) ; endproperty
assert property (SyncCheckeotid);

property SyncEqeotid; @(posedge clk_in_15) (A) == (B)  |-> (result) == (A) ; endproperty
assert property (SyncEqeotid);

endmodule