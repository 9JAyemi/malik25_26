module RegisterAdd_4_sva (
    input logic CLK,
    input logic in1,
    input logic in2,
    input logic out,
    input logic reset,
    input logic d0
);

property ResetSynceotid; @(posedge CLK) (reset) |-> out == 4'd0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge CLK) (reset) |-> out != in1 + in2 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge CLK) !reset |-> out == in1 + in2 ;endproperty
assert property (ResetSynceotid_3);

endmodule