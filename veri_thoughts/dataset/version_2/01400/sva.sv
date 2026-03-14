module verilog_module_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic out
);
    // Sample on any signal edge since RTL is purely combinational.
    default clocking cb @(
        posedge VPWR or negedge VPWR or
        posedge VGND or negedge VGND or
        posedge VPB  or negedge VPB  or
        posedge VNB  or negedge VNB  or
        posedge out  or negedge out
    ); endclocking

    // out equals logical AND of all inputs.
    check_out_matches_and: assert property (
        out == (VPWR & VGND & VPB & VNB)
    );

    // If out is HIGH, all inputs must be HIGH.
    check_out_high_implies_inputs_high: assert property (
        out |-> (VPWR && VGND && VPB && VNB)
    );

    // If all inputs are HIGH, out must be HIGH.
    check_all_high_implies_out_high: assert property (
        (VPWR && VGND && VPB && VNB) |-> out
    );

    // If any input is LOW, out must be LOW.
    check_any_low_implies_out_low: assert property (
        (!VPWR || !VGND || !VPB || !VNB) |-> !out
    );

    // On out rising edge, all inputs must be HIGH.
    check_out_rise_requires_all_ones: assert property (
        @(posedge out) (VPWR && VGND && VPB && VNB)
    );

    // On out falling edge, at least one input must be LOW.
    check_out_fall_requires_some_zero: assert property (
        @(negedge out) (!VPWR || !VGND || !VPB || !VNB)
    );

    // A falling VPWR forces out LOW.
    check_vpwr_fall_forces_out_low: assert property (
        @(negedge VPWR) !out
    );

    // A falling VGND forces out LOW.
    check_vgnd_fall_forces_out_low: assert property (
        @(negedge VGND) !out
    );

    // A falling VPB forces out LOW.
    check_vpb_fall_forces_out_low: assert property (
        @(negedge VPB) !out
    );

    // A falling VNB forces out LOW.
    check_vnb_fall_forces_out_low: assert property (
        @(negedge VNB) !out
    );
endmodule