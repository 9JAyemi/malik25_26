module sky130_fd_sc_ms__o2111a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    // X equals B1&C1&D1&(A1|A2) when A1 rises.
    check_eq_on_A1_posedge: assert property (
        @(posedge A1) X === (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals B1&C1&D1&(A1|A2) when A2 rises.
    check_eq_on_A2_posedge: assert property (
        @(posedge A2) X === (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals B1&C1&D1&(A1|A2) when B1 rises.
    check_eq_on_B1_posedge: assert property (
        @(posedge B1) X === (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals B1&C1&D1&(A1|A2) when C1 rises.
    check_eq_on_C1_posedge: assert property (
        @(posedge C1) X === (B1 & C1 & D1 & (A1 | A2))
    );

    // X equals B1&C1&D1&(A1|A2) when D1 rises.
    check_eq_on_D1_posedge: assert property (
        @(posedge D1) X === (B1 & C1 & D1 & (A1 | A2))
    );

    // Falling B1 forces X low through the AND gate.
    check_X_zero_on_B1_fall: assert property (
        @(negedge B1) X == 1'b0
    );

    // Falling C1 forces X low through the AND gate.
    check_X_zero_on_C1_fall: assert property (
        @(negedge C1) X == 1'b0
    );

    // Falling D1 forces X low through the AND gate.
    check_X_zero_on_D1_fall: assert property (
        @(negedge D1) X == 1'b0
    );

    // If A1 falls and A2 is 0, (A1|A2)=0 so X must be 0.
    check_X_zero_on_A1_fall_when_A2_zero: assert property (
        @(negedge A1) (!A2) |-> (X == 1'b0)
    );

    // If A2 falls and A1 is 0, (A1|A2)=0 so X must be 0.
    check_X_zero_on_A2_fall_when_A1_zero: assert property (
        @(negedge A2) (!A1) |-> (X == 1'b0)
    );
endmodule