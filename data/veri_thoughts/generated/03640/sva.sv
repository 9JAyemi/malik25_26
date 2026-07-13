module clk_gen_assertions #(
    parameter int DIVIDER = 4
) (
    input logic        clk_in1,
    input logic        reset,
    input logic        clk_out1,
    input logic [31:0] counter,
    input logic        clk_out1_reg
);

    // Reset clears the counter and drives the generated clock low.
    check_reset_clears_state: assert property (
        @(posedge clk_in1)
        reset |-> ((counter == 32'd0) && (clk_out1_reg == 1'b0) && (clk_out1 == 1'b0))
    );

    // The output port must mirror the internal clock register.
    check_output_matches_reg: assert property (
        @(posedge clk_in1) disable iff (reset)
        clk_out1 == clk_out1_reg
    );

    // Before the terminal count, the counter increments and the output holds.
    check_counter_increments_before_terminal: assert property (
        @(posedge clk_in1) disable iff (reset || $initstate)
        (counter != ((1 / DIVIDER) - 1)) |=> ((counter == ($past(counter) + 32'd1)) &&
                                              (clk_out1_reg == $past(clk_out1_reg)) &&
                                              (clk_out1 == $past(clk_out1)))
    );

    // At the terminal count, the counter clears and the output toggles.
    check_terminal_count_wraps_and_toggles: assert property (
        @(posedge clk_in1) disable iff (reset || $initstate)
        (counter == ((1 / DIVIDER) - 1)) |=> ((counter == 32'd0) &&
                                              (clk_out1_reg == ~$past(clk_out1_reg)) &&
                                              (clk_out1 == ~$past(clk_out1)))
    );

    // Any output transition must be caused by the previous terminal count.
    check_output_toggle_requires_terminal_count: assert property (
        @(posedge clk_in1) disable iff (reset || $initstate)
        (clk_out1 != $past(clk_out1)) |-> ($past(counter) == ((1 / DIVIDER) - 1))
    );

    // A nonzero-to-zero counter transition must come from the terminal count.
    check_counter_clear_requires_terminal_count: assert property (
        @(posedge clk_in1) disable iff (reset || $initstate)
        ((counter == 32'd0) && ($past(counter) != 32'd0)) |-> ($past(counter) == ((1 / DIVIDER) - 1))
    );

endmodule