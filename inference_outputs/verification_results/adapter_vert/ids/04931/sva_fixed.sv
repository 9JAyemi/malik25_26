module mux_4to1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S,
    input logic Y,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (S) == (2'b00) |-> (Y) == (C) ; endproperty
assert property (ClockSynceotid);

property DataSynceotid; @(posedge clk_in_1) (S) == (2'b01) |-> (Y) == (D) ; endproperty
assert property (DataSynceotid);

property ValidDataeotid; @(posedge clk_in_1) (S) == (2'b10) |-> (Y) == (A) ; endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (S) == (2'b11) |-> (Y) == (B) ; endproperty
assert property (ValidDataeotid_2);

endmodule