module sky130_fd_sc_hdll__a211o_sva (
    input logic CLK,   // External sampling clock (DUT has no clock/reset)
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // X implements (A1 & A2) | B1 | C1.
    check_function_equation: assert property (
        @(posedge CLK) X == ((A1 & A2) | B1 | C1)
    );

    // B1=1 forces X=1.
    check_b1_dominates: assert property (
        @(posedge CLK) (B1 == 1'b1) |-> (X == 1'b1)
    );

    // C1=1 forces X=1.
    check_c1_dominates: assert property (
        @(posedge CLK) (C1 == 1'b1) |-> (X == 1'b1)
    );

    // A1&A2=1 forces X=1.
    check_a1a2_implies_x1: assert property (
        @(posedge CLK) (A1 & A2) |-> (X == 1'b1)
    );

    // With B1=0 and C1=0, X equals A1&A2.
    check_reduce_when_b1c1_low: assert property (
        @(posedge CLK) ((B1 == 1'b0) && (C1 == 1'b0)) |-> (X == (A1 & A2))
    );

    // X=0 implies B1=0, C1=0, and not (A1&A2).
    check_x0_implies_inputs_low: assert property (
        @(posedge CLK) (X == 1'b0) |-> ((B1 == 1'b0) && (C1 == 1'b0) && !(A1 & A2))
    );

    // X=1 implies B1=1 or C1=1 or (A1&A2)=1.
    check_x1_implies_some_input_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((B1 == 1'b1) || (C1 == 1'b1) || (A1 & A2))
    );

    // If all inputs are stable, X must be stable.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge CLK) ($stable(A1) && $stable(A2) && $stable(B1) && $stable(C1)) |-> $stable(X)
    );

    // Rising B1 causes X=1 in the same cycle.
    check_rose_b1_forces_x1: assert property (
        @(posedge CLK) $rose(B1) |-> (X == 1'b1)
    );

    // Rising C1 causes X=1 in the same cycle.
    check_rose_c1_forces_x1: assert property (
        @(posedge CLK) $rose(C1) |-> (X == 1'b1)
    );
endmodule