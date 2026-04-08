module current_sva #(
    parameter int unsigned r = 100
) (
    input logic       ctrl,
    input logic [7:0] vref,
    input logic       isrc,
    input logic       isnk
);

    // isrc matches the selected source expression.
    check_isrc_function: assert property (
        @($global_clock) isrc == (ctrl ? ((vref / r) & 1) : 1'b0)
    );

    // isnk matches the selected sink expression.
    check_isnk_function: assert property (
        @($global_clock) isnk == (ctrl ? 1'b0 : ((vref / r) & 1))
    );

    // Source mode forces the sink output low.
    check_source_mode_disables_sink: assert property (
        @($global_clock) (ctrl == 1'b1) |-> (isnk == 1'b0)
    );

    // Sink mode forces the source output low.
    check_sink_mode_disables_source: assert property (
        @($global_clock) (ctrl == 1'b0) |-> (isrc == 1'b0)
    );

    // An even truncated division result leaves both outputs low.
    check_even_division_lsb_outputs_low: assert property (
        @($global_clock) (((vref / r) & 1) == 1'b0) |-> ((isrc == 1'b0) && (isnk == 1'b0))
    );

    // In source mode, an odd truncated division result raises only isrc.
    check_odd_division_source_mode: assert property (
        @($global_clock) ((ctrl == 1'b1) && (((vref / r) & 1) == 1'b1)) |-> ((isrc == 1'b1) && (isnk == 1'b0))
    );

    // In sink mode, an odd truncated division result raises only isnk.
    check_odd_division_sink_mode: assert property (
        @($global_clock) ((ctrl == 1'b0) && (((vref / r) & 1) == 1'b1)) |-> ((isrc == 1'b0) && (isnk == 1'b1))
    );

    // The two outputs are never high at the same time.
    check_outputs_mutually_exclusive: assert property (
        @($global_clock) !((isrc == 1'b1) && (isnk == 1'b1))
    );

endmodule