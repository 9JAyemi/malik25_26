module four_to_one_mux_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b00) |-> (out) == (in0) ; endproperty
assert property (ClockSynceotid);

property ValidDataeotid; @(posedge clk_in_1) (sel) == (2'b01) |-> (out) == (in1) ; endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (sel) == (2'b10) |-> (out) == (in2) ; endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_1) (sel) == (2'b11) |-> (out) == (in3) ; endproperty
assert property (ValidDataeotid_3);

endmodule