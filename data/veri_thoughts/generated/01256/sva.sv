module freq_synthesizer_sva #(
    parameter int unsigned N = 10,
    parameter int unsigned M = 5
) (
    input  logic         clk_ref,
    input  logic [31:0]  ctrl_word,
    input  logic         out_clk,
    input  logic [31:0]  counter,
    input  logic [31:0]  divider
);
    // Local copies of thresholds for comparisons
    localparam logic [31:0] N_MINUS_1 = N - 1;
    localparam logic [31:0] M_MINUS_1 = M - 1;

    // Gate assertions for the first cycle
    logic past_valid;
    initial past_valid = 1'b0;
    always @(posedge clk_ref) past_valid <= 1'b1;

    // Counter increments by 1 when not at N-1.
    check_counter_increment_when_not_wrap: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            ($past(counter) != N_MINUS_1) |-> (counter == $past(counter) + 32'd1)
    );

    // Counter wraps to 0 when at N-1.
    check_counter_wrap_to_zero: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            ($past(counter) == N_MINUS_1) |-> (counter == 32'd0)
    );

    // Divider holds when counter does not wrap.
    check_divider_stable_when_counter_not_wrap: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            ($past(counter) != N_MINUS_1) |-> (divider == $past(divider))
    );

    // out_clk holds when counter does not wrap.
    check_outclk_stable_when_counter_not_wrap: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            ($past(counter) != N_MINUS_1) |-> (out_clk == $past(out_clk))
    );

    // On counter wrap without divider wrap, divider increments and out_clk holds.
    check_divider_inc_on_counter_wrap_not_div_wrap: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            ($past(counter) == N_MINUS_1 && $past(divider) != M_MINUS_1)
            |-> (divider == $past(divider) + 32'd1) && (out_clk == $past(out_clk))
    );

    // On both counter and divider wrap, divider resets and out_clk toggles.
    check_both_wrap_resets_divider_and_toggles_outclk: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            ($past(counter) == N_MINUS_1 && $past(divider) == M_MINUS_1)
            |-> (divider == 32'd0) && (out_clk == ~$past(out_clk))
    );

    // On any counter wrap, only valid divider/out_clk updates occur (increment+hold or reset+toggle).
    check_counter_wrap_results_in_valid_update: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            ($past(counter) == N_MINUS_1)
            |-> (
                    ((divider == $past(divider) + 32'd1) && (out_clk == $past(out_clk))) ||
                    ((divider == 32'd0) && (out_clk == ~$past(out_clk)))
                )
    );

    // out_clk can only change when both counter and divider were at their terminal values.
    check_outclk_toggle_only_on_both_wraps: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            $changed(out_clk) |-> ($past(counter) == N_MINUS_1) && ($past(divider) == M_MINUS_1)
    );

    // Any change of divider implies counter wrapped the previous cycle.
    check_divider_change_implies_counter_wrap: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            (divider != $past(divider)) |-> ($past(counter) == N_MINUS_1)
    );

    // out_clk cannot toggle in back-to-back cycles.
    check_no_back_to_back_outclk_toggle: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            $changed(out_clk) |-> ##1 !$changed(out_clk)
    );

    // Any change of out_clk must be a logical inversion.
    check_outclk_change_is_invert: assert property (
        @(posedge clk_ref) disable iff (!past_valid)
            $changed(out_clk) |-> (out_clk == ~$past(out_clk))
    );

endmodule