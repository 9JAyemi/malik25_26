module dff_sva (
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic RESET_B,
    input logic Q,
    input logic Q_B
);

    // A sampled low reset forces the reset state by the next cycle.
    check_reset_state: assert property (
        @(posedge CLK)
        !RESET_B |=> ((Q == 1'b0) && (Q_B == 1'b1))
    );

    // SCD sets the outputs when asserted alone.
    check_scd_sets_outputs: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (SCD && !SCE) |=> ((Q == 1'b1) && (Q_B == 1'b0))
    );

    // SCD has priority over SCE when both are asserted.
    check_scd_priority_over_sce: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (SCD && SCE) |=> ((Q == 1'b1) && (Q_B == 1'b0))
    );

    // SCE loads a 1 from D when SCD is low.
    check_sce_loads_one: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!SCD && SCE && D) |=> ((Q == 1'b1) && (Q_B == 1'b0))
    );

    // SCE loads a 0 from D when SCD is low.
    check_sce_loads_zero: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!SCD && SCE && !D) |=> ((Q == 1'b0) && (Q_B == 1'b1))
    );

    // With both controls low, the current state is held.
    check_hold_when_controls_low: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!SCD && !SCE) |=> ((Q == $past(Q)) && (Q_B == $past(Q_B)))
    );

endmodule