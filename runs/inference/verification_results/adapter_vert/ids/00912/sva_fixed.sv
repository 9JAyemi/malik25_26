module shift_register_4bit_sva (
    input logic CLK,
    input logic CLR,
    input logic D,
    input logic LOAD,
    input logic Q,
    input logic Q_next,
    input logic b0000
);

property ResetSynceotid; @(posedge CLK) (CLR) |-> (Q == 4'b0000) && (Q_next == 4'b0000) ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge CLK) (LOAD) && !(CLR)  |-> (Q == D) && (Q_next == D) ;endproperty
assert property (LoadSynceotid);

property ShiftSynceotid; @(posedge CLK) ( !LOAD ) && !(CLR)  |-> (Q == {Q[2:0], D[3]}) && (Q_next == {Q[2:0], D[3]});endproperty
assert property (ShiftSynceotid);

endmodule