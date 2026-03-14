module sky130_fd_sc_ls__clkdlyinv5sd2_sva (
    input logic CLK,   // sampling clock for assertions
    input logic Y,     // DUT output
    input logic A      // DUT input
);
    // Y is always the logical inversion of A at sample time.
    check_inversion_function: assert property (
        @(posedge CLK) (Y === ~A)
    );

    // A rising edge implies a falling edge on Y.
    check_roseA_fellY: assert property (
        @(posedge CLK) $rose(A) |-> $fell(Y)
    );

    // A falling edge implies a rising edge on Y.
    check_fellA_roseY: assert property (
        @(posedge CLK) $fell(A) |-> $rose(Y)
    );

    // Y rising edge implies a falling edge on A.
    check_roseY_fellA: assert property (
        @(posedge CLK) $rose(Y) |-> $fell(A)
    );

    // Y falling edge implies a rising edge on A.
    check_fellY_roseA: assert property (
        @(posedge CLK) $fell(Y) |-> $rose(A)
    );

    // If A is stable across samples, Y is stable across samples.
    check_stable_A_implies_stable_Y: assert property (
        @(posedge CLK) $stable(A) |-> $stable(Y)
    );

    // When A is known at consecutive samples, A and Y change iff each other changes.
    check_change_equivalence_when_known: assert property (
        @(posedge CLK)
            (((A === 1'b0) || (A === 1'b1)) && (($past(A) === 1'b0) || ($past(A) === 1'b1)))
            |-> ($changed(Y) == $changed(A))
    );

    // Y is never high-impedance (no tri-state drivers in DUT).
    check_Y_not_highz: assert property (
        @(posedge CLK) (Y !== 1'bz)
    );

    // When A is 0, Y must be 1.
    check_A0_implies_Y1: assert property (
        @(posedge CLK) (A === 1'b0) |-> (Y === 1'b1)
    );

    // When A is 1, Y must be 0.
    check_A1_implies_Y0: assert property (
        @(posedge CLK) (A === 1'b1) |-> (Y === 1'b0)
    );
endmodule