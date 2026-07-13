module sky130_fd_sc_ls__o21a_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    output logic X
);
    // The logic is purely combinational, so we will use @(posedge CLK) for assertions.

    // A1 and A2 must both be 0 for X to be 0.
    check_X_low_when_A1_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b1) || (A2 == 1'b1) |-> (X == 1'b1)
    );

    // B1 must be 1 for X to be 1.
    check_X_high_when_B1_high: assert property (
        @(posedge CLK) (B1 == 1'b1) |-> (X == 1'b1)
    );

    // A1 and A2 must both be 0 for X to be 0.
    check_X_low_when_A1_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b1) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b0) |-> (X == 1'b1)
    );

    // B1 must be 0 for X to be 0.
    check_X_low_when_B1_low: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // A1 and A2 must both be 0 for X to be 0.
    check_X_low_when_A1_low_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // B1 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b0) |-> (X == 1'b1)
    );

    // B1 must be 0 for X to be 0.
    check_X_low_when_B1_low: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // A1 and A2 must both be 0 for X to be 0.
    check_X_low_when_A1_low_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // B1 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b0) |-> (X == 1'b1)
    );

    // B1 must be 0 for X to be 0.
    check_X_low_when_B1_low: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // A1 and A2 must both be 0 for X to be 0.
    check_X_low_when_A1_low_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // B1 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b0) |-> (X == 1'b1)
    );

    // B1 must be 0 for X to be 0.
    check_X_low_when_B1_low: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // A1 and A2 must both be 0 for X to be 0.
    check_X_low_when_A1_low_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b1) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // B1 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_low: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_low_A2_high: assert property (
        @(posedge CLK) (A1 == 1'b0) && (A2 == 1'b1) |-> (X == 1'b1)
    );

    // A1 or A2 must be 1 for X to be 1.
    check_X_high_when_A1_high_A2_low: assert property (
        @(posed