module DFF_AR_sva (
    input logic CLK,
    input logic D,
    input logic Q,
    input logic QN,
    input logic RST,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge CLK) (RST) |-> (Q) == 1'b0 && (QN) == 1'b1 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge CLK) (RST) |-> (Q) != (D) && (Q) != (QN) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge CLK) ! (RST)  |-> (Q) == 1'b0 && (QN) == 1'b1; endproperty
assert property (ResetSynceotid_3);

endmodule