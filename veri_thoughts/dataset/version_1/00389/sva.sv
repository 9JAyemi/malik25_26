module sky130_fd_sc_ls__einvp_sva (
    input logic Z,
    input logic A,
    input logic TE
);

    // Rising enable drives the inverted input onto Z.
    check_enable_drives_inverted_input: assert property (
        @(posedge TE) (Z === ~A)
    );

    // Falling enable releases Z to high impedance.
    check_disable_releases_output: assert property (
        @(negedge TE) (Z === 1'bz)
    );

    // With enable high, a rising A drives Z low.
    check_enabled_rising_input_drives_low: assert property (
        @(posedge A) (TE === 1'b1) |-> (Z === 1'b0)
    );

    // With enable low, a rising A leaves Z high impedance.
    check_disabled_rising_input_keeps_high_z: assert property (
        @(posedge A) (TE === 1'b0) |-> (Z === 1'bz)
    );

    // With enable high, a falling A drives Z high.
    check_enabled_falling_input_drives_high: assert property (
        @(negedge A) (TE === 1'b1) |-> (Z === 1'b1)
    );

    // With enable low, a falling A leaves Z high impedance.
    check_disabled_falling_input_keeps_high_z: assert property (
        @(negedge A) (TE === 1'b0) |-> (Z === 1'bz)
    );

endmodule