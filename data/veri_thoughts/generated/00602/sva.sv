module synchronizer_sva #(
    parameter DW = 32
) (
    input  logic               clk,
    input  logic               reset,       // Active-HIGH asynchronous reset
    input  logic [DW-1:0]      in,
    input  logic [DW-1:0]      out,
    input  logic [DW-1:0]      sync_reg0
);

    ///// Reset behavior /////
    // When reset is HIGH at a clock edge, both pipeline registers are driven to zero.
    check_reset_clears_regs: assert property (
        @(posedge clk) reset |-> (out == '0) && (sync_reg0 == '0)
    );

    // If reset is held HIGH across consecutive clock edges, both registers remain zero.
    check_reset_hold_zeros: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (out == '0) && (sync_reg0 == '0)
    );

    // On a synchronous rising edge of reset at the clock, both registers must be zero.
    check_reset_rise_clears: assert property (
        @(posedge clk) $rose(reset) |-> (out == '0) && (sync_reg0 == '0)
    );

    // On a synchronous falling edge of reset at the clock, out remains zero in that cycle.
    check_reset_fall_out_zero: assert property (
        @(posedge clk) $fell(reset) |-> (out == '0)
    );

    // If the previous cycle had reset asserted, out must be zero in the current cycle.
    check_post_reset_out_zero: assert property (
        @(posedge clk) $past(reset) |-> (out == '0)
    );

    ///// Functional behavior /////
    // Stage 1 always samples input when not in reset.
    check_stage1_samples_input: assert property (
        @(posedge clk) disable iff (reset) (sync_reg0 == in)
    );

    // If input was zero two cycles ago, out must be zero now (reset can only force zeros).
    check_zero_propagates_two_cycles: assert property (
        @(posedge clk) ($past(in,2) == '0) |-> (out == '0)
    );

endmodule