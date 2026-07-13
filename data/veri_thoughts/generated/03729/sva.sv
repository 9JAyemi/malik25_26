module sky130_fd_sc_lp__invlp_sva (
    input logic A,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // Output is always the inversion of A.
    check_inverter_function: assert property (
        @($global_clock) (Y === ~A)
    );

    // A low input produces a high output.
    check_low_input_drives_high_output: assert property (
        @($global_clock) (A === 1'b0) |-> (Y === 1'b1)
    );

    // A high input produces a low output.
    check_high_input_drives_low_output: assert property (
        @($global_clock) (A === 1'b1) |-> (Y === 1'b0)
    );

    // If A does not change, Y does not change.
    check_stable_input_keeps_output_stable: assert property (
        @($global_clock) $stable(A) |-> $stable(Y)
    );

    // Any output change must be caused by an input change.
    check_output_change_requires_input_change: assert property (
        @($global_clock) $changed(Y) |-> $changed(A)
    );

    // Power-pin changes do not affect Y when A is unchanged.
    check_power_pins_do_not_affect_logic_function: assert property (
        @($global_clock)
        ($stable(A) && ($changed(VPB) || $changed(VPWR) || $changed(VGND) || $changed(VNB)))
        |-> $stable(Y)
    );

endmodule