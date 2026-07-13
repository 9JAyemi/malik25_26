module power_management_sva (
    (* gclk *) input logic clk,
    input logic VIRTPWR,
    input logic SLEEP,
    input logic VPWR,
    input logic VPB,
    input logic VNB
);

    // SLEEP asserted forces virtual power low.
    check_sleep_forces_off: assert property (
        @(posedge clk) SLEEP |-> !VIRTPWR
    );

    // Loss of VPWR forces virtual power low.
    check_vpwr_loss_forces_off: assert property (
        @(posedge clk) !VPWR |-> !VIRTPWR
    );

    // Loss of VPB forces virtual power low.
    check_vpb_loss_forces_off: assert property (
        @(posedge clk) !VPB |-> !VIRTPWR
    );

    // Loss of VNB forces virtual power low.
    check_vnb_loss_forces_off: assert property (
        @(posedge clk) !VNB |-> !VIRTPWR
    );

    // All valid inputs drive virtual power high.
    check_all_conditions_enable_power: assert property (
        @(posedge clk) (!SLEEP && VPWR && VPB && VNB) |-> VIRTPWR
    );

    // Virtual power high requires all inputs to be valid.
    check_output_high_requires_valid_inputs: assert property (
        @(posedge clk) VIRTPWR |-> (!SLEEP && VPWR && VPB && VNB)
    );

    // Virtual power low requires at least one disabling condition.
    check_output_low_requires_disable_condition: assert property (
        @(posedge clk) !VIRTPWR |-> (SLEEP || !VPWR || !VPB || !VNB)
    );

    // Output matches the implemented combinational equation.
    check_output_matches_equation: assert property (
        @(posedge clk) VIRTPWR == (!SLEEP && VPWR && VPB && VNB)
    );

endmodule