module flip_flop_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic DE,
    input logic SCD,
    input logic SCE,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // When scan is disabled, the output is forced low.
    check_output_zero_when_scan_disabled: assert property (
        @(posedge CLK) (!SCE || SCD) |-> (Q == 1'b0)
    );

    // A high output is only possible when scan is enabled.
    check_q_high_requires_scan_enabled: assert property (
        @(posedge CLK) Q |-> (SCE && !SCD)
    );

    // A qualified load is visible on Q one cycle later if scan stays enabled.
    check_load_updates_q_when_visible: assert property (
        @(posedge CLK) (SCE && !SCD && DE) |=> ((!SCE || SCD) || (Q == $past(D)))
    );

    // Without a qualified load, Q holds its visible value across enabled cycles.
    check_hold_across_enabled_cycles_without_load: assert property (
        @(posedge CLK) (SCE && !SCD && !DE) |=> ((!SCE || SCD) || (Q == $past(Q)))
    );

    // Any visible change on Q across enabled cycles requires a prior load.
    check_visible_q_change_requires_load: assert property (
        @(posedge CLK) ($past(SCE && !SCD) && (SCE && !SCD) && (Q != $past(Q))) |-> $past(DE)
    );

    // VPWR is tied high by the RTL.
    check_vpwr_tied_high: assert property (
        @(posedge CLK) (VPWR == 1'b1)
    );

    // VGND is tied low by the RTL.
    check_vgnd_tied_low: assert property (
        @(posedge CLK) (VGND == 1'b0)
    );

    // VPB is tied high by the RTL.
    check_vpb_tied_high: assert property (
        @(posedge CLK) (VPB == 1'b1)
    );

    // VNB is tied low by the RTL.
    check_vnb_tied_low: assert property (
        @(posedge CLK) (VNB == 1'b0)
    );

endmodule