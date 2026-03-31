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

    // Q follows the RTL next-state function.
    check_next_state_function: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |=> (Q == ($past(DE) ? $past(D) : ($past(SCE) ? $past(SCD) : $past(Q))))
    );

    // DE has highest priority and loads D on the next cycle.
    check_de_loads_d: assert property (
        @(posedge CLK) disable iff (1'b0)
        DE |=> (Q == $past(D))
    );

    // With DE low, SCE loads SCD on the next cycle.
    check_sce_loads_scd_when_de_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!DE && SCE) |=> (Q == $past(SCD))
    );

    // With DE and SCE low, Q holds its previous value.
    check_hold_when_both_controls_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!DE && !SCE) |=> (Q == $past(Q))
    );

endmodule