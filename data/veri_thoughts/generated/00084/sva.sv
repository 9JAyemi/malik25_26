module constant_voltage_driver_sva (
    input logic clk,
    input logic control,
    input logic [7:0] vref,
    input logic vout
);

    // When control is low, the output must be low.
    check_output_zero_when_control_low: assert property (
        @(posedge clk) (control === 1'b0) |-> (vout === 1'b0)
    );

    // When control is high, the output must match the vref LSB.
    check_output_tracks_vref_lsb_when_control_high: assert property (
        @(posedge clk) (control === 1'b1) |-> (vout === vref[0])
    );

    // A high output requires control high and vref[0] high.
    check_high_output_requires_enable_and_lsb: assert property (
        @(posedge clk) (vout === 1'b1) |-> ((control === 1'b1) && (vref[0] === 1'b1))
    );

    // Changes in vref must not affect the output while control stays low.
    check_vref_ignored_when_control_low: assert property (
        @(posedge clk)
        ($past(control) === 1'b0) && (control === 1'b0) &&
        ($past(vref) !== vref) |-> $stable(vout)
    );

    // Changes in vref[7:1] alone must not affect the output while enabled.
    check_upper_vref_bits_do_not_affect_output: assert property (
        @(posedge clk)
        ($past(control) === 1'b1) && (control === 1'b1) &&
        ($past(vref[0]) === vref[0]) &&
        ($past(vref[7:1]) !== vref[7:1]) |-> $stable(vout)
    );

    // A change in vref[0] must change the output while enabled and upper bits stay the same.
    check_lsb_change_updates_output_when_enabled: assert property (
        @(posedge clk)
        ($past(control) === 1'b1) && (control === 1'b1) &&
        ($past(vref[7:1]) === vref[7:1]) &&
        ($past(vref[0]) !== vref[0]) |-> (vout !== $past(vout))
    );

endmodule