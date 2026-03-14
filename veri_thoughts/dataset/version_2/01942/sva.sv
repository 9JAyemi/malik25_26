module sky130_fd_sc_ms__clkdlyinv3sd2_sva (
    input logic CLK, // Sampling clock for assertions (DUT has no clock/reset)
    input logic A,   // DUT input
    input logic Y    // DUT output
);
    // Y must be the bitwise inversion of A at every sample.
    check_y_is_invert_of_a: assert property (
        @(posedge CLK) (Y === ~A)
    );

    // A rising edge implies Y falls at the same sample.
    check_rise_a_fall_y: assert property (
        @(posedge CLK) $rose(A) |-> $fell(Y)
    );

    // A falling edge implies Y rises at the same sample.
    check_fall_a_rise_y: assert property (
        @(posedge CLK) $fell(A) |-> $rose(Y)
    );

    // If A is stable across a cycle, Y must also be stable.
    check_stability_when_a_stable: assert property (
        @(posedge CLK) $stable(A) |-> $stable(Y)
    );

    // Y cannot change unless A changed in that cycle.
    check_no_spurious_y_changes: assert property (
        @(posedge CLK) $changed(Y) |-> $changed(A)
    );

    // Any change in A must cause a change in Y in that cycle.
    check_a_change_causes_y_change: assert property (
        @(posedge CLK) $changed(A) |-> $changed(Y)
    );
endmodule