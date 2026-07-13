module power_fill_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic power_out
);

    // power_out matches the OR of all power pins.
    check_power_out_matches_or: assert property (
        @($global_clock) power_out == (VPWR || VGND || VPB || VNB)
    );

    // Any asserted power pin drives power_out high.
    check_any_input_high_sets_output: assert property (
        @($global_clock) (VPWR || VGND || VPB || VNB) |-> power_out
    );

    // With all power pins low, power_out is low.
    check_all_inputs_low_clears_output: assert property (
        @($global_clock) !(VPWR || VGND || VPB || VNB) |-> !power_out
    );

    // A high power_out requires at least one power pin high.
    check_output_high_implies_input_high: assert property (
        @($global_clock) power_out |-> (VPWR || VGND || VPB || VNB)
    );

    // A low power_out requires all power pins low.
    check_output_low_implies_inputs_low: assert property (
        @($global_clock) !power_out |-> !(VPWR || VGND || VPB || VNB)
    );

endmodule