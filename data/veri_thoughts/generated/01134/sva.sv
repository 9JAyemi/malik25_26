module sky130_fd_sc_ms__a311oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // No clock/reset in DUT; pure combinational: Y = ~((A1 & A2 & A3) | B1 | C1). Sample on posedge A1.

    // Y equals the NOR of (A1&A2&A3), B1, and C1.
    check_function_equation: assert property (
        @(posedge A1) Y == ~((A1 & A2 & A3) | B1 | C1)
    );

    // B1 high forces Y low.
    check_B1_high_forces_Y0: assert property (
        @(posedge A1) B1 |-> (Y == 1'b0)
    );

    // C1 high forces Y low.
    check_C1_high_forces_Y0: assert property (
        @(posedge A1) C1 |-> (Y == 1'b0)
    );

    // All A inputs high forces Y low (when B1 and C1 are irrelevant).
    check_allA_high_forces_Y0: assert property (
        @(posedge A1) (A1 & A2 & A3) |-> (Y == 1'b0)
    );

    // If the OR of (A1&A2&A3), B1, or C1 is high, Y must be low.
    check_or_inputs_high_implies_Y0: assert property (
        @(posedge A1) ((A1 & A2 & A3) | B1 | C1) |-> (Y == 1'b0)
    );

    // Y high requires B1 and C1 low and not all A inputs high.
    check_Y1_requires_conditions: assert property (
        @(posedge A1) (Y == 1'b1) |-> ((~B1) & (~C1) & ~(A1 & A2 & A3))
    );

    // Y low implies at least one of (A1&A2&A3), B1, or C1 is high.
    check_Y0_implies_some_input_high: assert property (
        @(posedge A1) (Y == 1'b0) |-> ((A1 & A2 & A3) | B1 | C1)
    );

    // With B1=C1=0, Y equals NAND of A1,A2,A3.
    check_BC_zero_reduces_to_NAND3: assert property (
        @(posedge A1) ((~B1) & (~C1)) |-> (Y == ~(A1 & A2 & A3))
    );

    // With B1=C1=0 and Y low, all A inputs must be high.
    check_BC_zero_Y0_implies_allA_high: assert property (
        @(posedge A1) ((~B1) & (~C1) & (Y == 1'b0)) |-> (A1 & A2 & A3)
    );

    // With B1=C1=0 and Y high, not all A inputs are high.
    check_BC_zero_Y1_implies_not_allA_high: assert property (
        @(posedge A1) ((~B1) & (~C1) & (Y == 1'b1)) |-> ~(A1 & A2 & A3)
    );

endmodule