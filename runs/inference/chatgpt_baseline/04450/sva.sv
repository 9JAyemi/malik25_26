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

    // Q follows the RTL next-state function across clock edges.
    check_next_state_function: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |=> Q == ($past(DE) ? $past(D) : ($past(SCE) ? $past(SCD) : $past(Q)))
    );

    // Q captures D when only DE is asserted.
    check_capture_d_when_de_only: assert property (
        @(posedge CLK) disable iff (1'b0)
        (DE && !SCE) |=> Q == $past(D)
    );

    // DE has priority over SCE when both enables are asserted.
    check_de_priority_over_sce: assert property (
        @(posedge CLK) disable iff (1'b0)
        (DE && SCE) |=> Q == $past(D)
    );

    // Q captures SCD when scan enable is asserted without DE.
    check_capture_scd_when_sce_only: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!DE && SCE) |=> Q == $past(SCD)
    );

    // Q holds its value when neither enable is asserted.
    check_hold_when_no_enable: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!DE && !SCE) |=> Q == $past(Q)
    );

    // Q can only change after a clock edge with DE or SCE asserted.
    check_change_requires_enable: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |=> (!$changed(Q) || ($past(DE) || $past(SCE)))
    );

endmodule