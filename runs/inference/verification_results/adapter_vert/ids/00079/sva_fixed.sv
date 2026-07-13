module mux_4to1_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel,
    input logic b0,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b00) |-> (out) == (in0) ; endproperty
assert property (ClockSynceotid);

property ValidIneotid; @(posedge clk_in_1) (sel) == (2'b01) |-> (out) == (in1) ; endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (sel) == (2'b10) |-> (out) == (in2) ; endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_1) (sel) == (2'b11) |-> (out) == (in3) ; endproperty
assert property (ValidIneotid_3);

property ValidIneotid_4; @(posedge clk_in_1) (sel) != 2'b00 && (sel) != 2'b01 && (sel) != 2'b10 && (sel) != 2'b11  |-> (out) == 4'b0 ; endproperty
assert property (ValidIneotid_4);

endmodule