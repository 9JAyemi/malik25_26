module digital_circuit_sva (
    input logic CLK,
    input logic D_ff,
    input logic Q,
    input logic Q_N,
    input logic Q_ff,
    input logic SCD,
    input logic SCE,
    input logic b1
);

property ClockSynceotid; @(posedge CLK) (SCE) |-> (D_ff == SCD) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge CLK) (SCE) != 1'b1  |-> (Q_ff == D_ff) ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge CLK) (SCE) != 1'b1  |-> (Q == Q_ff) ;endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge CLK) (SCE) != 1'b1  |-> (Q_N == ~Q_ff) ;endproperty
assert property (ClockSynceotid_4);

endmodule