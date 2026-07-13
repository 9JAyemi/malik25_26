module sky130_fd_sc_lp__xor2_sva (
    input logic A,
    input logic B,
    input logic X
);

    // Output matches the XOR of the two inputs.
    check_x_matches_xor: assert property (
        @($global_clock) X === (A ^ B)
    );

    // Both LOW inputs drive a LOW output.
    check_both_low_drive_low: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b0)) |-> (X === 1'b0)
    );

    // Both HIGH inputs drive a LOW output.
    check_both_high_drive_low: assert property (
        @($global_clock) ((A === 1'b1) && (B === 1'b1)) |-> (X === 1'b0)
    );

    // Different known inputs drive a HIGH output.
    check_inputs_differ_drive_high: assert property (
        @($global_clock) (((A === 1'b0) && (B === 1'b1)) || ((A === 1'b1) && (B === 1'b0))) |-> (X === 1'b1)
    );

    // Stable inputs keep the output stable across samples.
    check_stable_inputs_hold_output: assert property (
        @($global_clock) ($stable(A) && $stable(B)) |-> $stable(X)
    );

endmodule