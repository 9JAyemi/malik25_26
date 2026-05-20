module decoder_2to4_sva (
    input logic in,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (in) == (2'b00) |-> (out0) == 1 && (out1) == 0 && (out2) == 0 && (out3) == 0 ; endproperty
assert property (ClockSynceotid);

property ValidIneotid; @(posedge clk_in_1) (in) == (2'b01) |-> (out0) == 0 && (out1) == 1 && (out2) == 0 && (out3) == 0 ; endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (in) == (2'b10) |-> (out0) == 0 && (out1) == 0 && (out2) == 1 && (out3) == 0 ; endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_1) (in) == (2'b11) |-> (out0) == 0 && (out1) == 0 && (out2) == 0 && (out3) == 1 ; endproperty
assert property (ValidIneotid_3);

endmodule