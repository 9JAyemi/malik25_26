module combinational_circuit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [1:0] A1A2,
    input logic [1:0] B1B2,
    input logic [1:0] C1C2,
    input logic Y
);
    // Y equals (A0 & B0) | ~C0 (LSB function as coded).
    check_y_function: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ((A1A2[0] & B1B2[0]) | (~(C1C2[0])))
    );

    // C0=0 forces Y=1 regardless of A0,B0.
    check_c0_low_forces_y1: assert property (
        @(posedge CLK) disable iff (!RESETn) (C1C2[0] == 1'b0) |-> (Y == 1'b1)
    );

    // With C0=1, Y reduces to A0 & B0.
    check_c0_high_reduces_to_and: assert property (
        @(posedge CLK) disable iff (!RESETn) (C1C2[0] == 1'b1) |-> (Y == (A1A2[0] & B1B2[0]))
    );

    // A0 & B0 = 1 guarantees Y=1.
    check_and1_implies_y1: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1A2[0] & B1B2[0]) == 1'b1) |-> (Y == 1'b1)
    );

    // If C0=1 and A0 & B0 = 0, then Y=0.
    check_c1_and_and0_implies_y0: assert property (
        @(posedge CLK) disable iff (!RESETn) ((C1C2[0] == 1'b1) && ((A1A2[0] & B1B2[0]) == 1'b0)) |-> (Y == 1'b0)
    );

    // Y=0 only when C0=1 and A0 & B0 = 0.
    check_y0_only_under_conditions: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b0) |-> ((C1C2[0] == 1'b1) && ((A1A2[0] & B1B2[0]) == 1'b0))
    );

    // Y=1 implies either A0 & B0 = 1 or C0=0.
    check_y1_implies_conditions: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b1) |-> (((A1A2[0] & B1B2[0]) == 1'b1) || (C1C2[0] == 1'b0))
    );

    // If LSBs are stable across a cycle, Y must be stable.
    check_lsb_stable_implies_y_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(A1A2[0]) && $stable(B1B2[0]) && $stable(C1C2[0])) |-> $stable(Y)
    );

    // If Y changes, at least one LSB input bit changed.
    check_y_change_implies_lsb_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(Y) |-> ($changed(A1A2[0]) || $changed(B1B2[0]) || $changed(C1C2[0]))
    );

    // When A0 & B0 = 0, Y reduces to ~C0.
    check_and0_reduces_to_not_c0: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1A2[0] & B1B2[0]) == 1'b0) |-> (Y == (~(C1C2[0])))
    );
endmodule