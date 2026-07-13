module sky130_fd_sc_ms__clkdlyinv5sd3_sva (
    input logic CLK,
    input logic A,
    input logic Y
);
    // Y is the logical inversion of A at each sample.
    check_inversion_function: assert property (
        @(posedge CLK) (Y == ~A)
    );

    // Rising A implies falling Y at the same sample.
    check_rise_A_fall_Y: assert property (
        @(posedge CLK) $rose(A) |-> $fell(Y)
    );

    // Falling A implies rising Y at the same sample.
    check_fall_A_rise_Y: assert property (
        @(posedge CLK) $fell(A) |-> $rose(Y)
    );

    // Y and A are never equal at the sample.
    check_Y_not_equal_A: assert property (
        @(posedge CLK) (Y != A)
    );

    // If A changes between samples, Y must change as well.
    check_A_change_implies_Y_change: assert property (
        @(posedge CLK) $changed(A) |-> $changed(Y)
    );

    // If Y changes between samples, A must change as well.
    check_Y_change_implies_A_change: assert property (
        @(posedge CLK) $changed(Y) |-> $changed(A)
    );

    // When A is 0 at a sample, Y must be 1.
    check_A0_Y1: assert property (
        @(posedge CLK) (A == 1'b0) |-> (Y == 1'b1)
    );

    // When A is 1 at a sample, Y must be 0.
    check_A1_Y0: assert property (
        @(posedge CLK) (A == 1'b1) |-> (Y == 1'b0)
    );
endmodule