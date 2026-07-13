module sky130_fd_sc_hd__einvp_sva (
    input logic Z,
    input logic A,
    input logic TE
);

    // Enabled with A low drives Z high.
    check_enabled_low_input_drives_high: assert property (
        @($global_clock) ((TE === 1'b1) && (A === 1'b0)) |-> (Z === 1'b1)
    );

    // Enabled with A high drives Z low.
    check_enabled_high_input_drives_low: assert property (
        @($global_clock) ((TE === 1'b1) && (A === 1'b1)) |-> (Z === 1'b0)
    );

    // Disabled operation forces Z to high impedance.
    check_disabled_highz: assert property (
        @($global_clock) (TE === 1'b0) |-> (Z === 1'bz)
    );

    // A high-impedance output only occurs when disabled.
    check_highz_only_when_disabled: assert property (
        @($global_clock) (Z === 1'bz) |-> (TE === 1'b0)
    );

    // A low output requires enabled inversion of a high input.
    check_low_output_requires_enabled_high_input: assert property (
        @($global_clock) (Z === 1'b0) |-> ((TE === 1'b1) && (A === 1'b1))
    );

    // A high output requires enabled inversion of a low input.
    check_high_output_requires_enabled_low_input: assert property (
        @($global_clock) (Z === 1'b1) |-> ((TE === 1'b1) && (A === 1'b0))
    );

endmodule