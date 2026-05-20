module inverter_sva (
    input logic A,
    input logic B,
    input logic I,
    input logic O,
    input logic Y,
    input logic b0,
    input logic b1,
    input logic clk_in_13
);

property ClockInveotid; @(posedge clk_in_13) (I) |-> (O) == 1'b0 ; endproperty
assert property (ClockInveotid);

property ANDsynceotid; @(posedge clk_in_13) (A) &&  (B) |-> (Y) ; endproperty
assert property (ANDsynceotid);

property ValidDataeotid; @(posedge clk_in_13) (A) !=  (B)  |-> (Y) == 1'b1 ; endproperty
assert property (ValidDataeotid);

endmodule