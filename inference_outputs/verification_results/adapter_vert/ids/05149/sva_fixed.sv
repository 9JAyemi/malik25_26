module comparator_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic EQ,
    input logic GT,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (A) == (B) && (B) == (C) && (C) == (D) |-> (EQ) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (A) != (B) || (C) != (D) |-> (GT) ; endproperty
assert property (ClockSynceotid_2);

endmodule