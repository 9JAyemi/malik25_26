module sky130_fd_sc_ms__o211ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // Boolean function: Y = ~(C1 & (A1 | A2) & B1)
    check_boolean_function: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1)
        Y == ~(C1 & (A1 | A2) & B1)
    );

    // C1 LOW forces Y HIGH.
    check_c1_low_forces_y_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1)
        (!C1) |-> (Y == 1'b1)
    );

    // B1 LOW forces Y HIGH.
    check_b1_low_forces_y_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1)
        (!B1) |-> (Y == 1'b1)
    );

    // Both A inputs LOW force Y HIGH.
    check_both_a_low_force_y_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1)
        (!A1 && !A2) |-> (Y == 1'b1)
    );

    // With B1 and C1 HIGH, Y equals NOR of A1 and A2.
    check_y_as_nor_when_bc_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1)
        (B1 && C1) |-> (Y == (~A1 & ~A2))
    );

    // With A1 or A2 HIGH, Y equals ~(C1 & B1).
    check_y_reduces_when_a_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1)
        (A1 || A2) |-> (Y == ~(C1 & B1))
    );

    // Y LOW implies C1 and B1 HIGH and (A1 or A2) HIGH.
    check_y_low_condition: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1)
        (Y == 1'b0) |-> (C1 && B1 && (A1 || A2))
    );

    // Y HIGH implies at least one of C1 LOW, B1 LOW, or both A inputs LOW.
    check_y_high_condition: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1)
        (Y == 1'b1) |-> (!C1 || !B1 || (!A1 && !A2))
    );
endmodule