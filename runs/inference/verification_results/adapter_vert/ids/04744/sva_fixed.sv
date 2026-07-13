module mux_4to1_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic select,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_11
);

property ClockSynceotid; @(posedge clk_in_11) (select) == (2'b00) |-> (out) == (in0) ; endproperty
assert property (ClockSynceotid);

property ValidIneotid; @(posedge clk_in_11) (select) == (2'b01) |-> (out) == (in1) ; endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_11) (select) == (2'b10) |-> (out) == (in2) ; endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_11) (select) == (2'b11) |-> (out) == (in3) ; endproperty
assert property (ValidIneotid_3);

endmodule