module clk32to40_sva (
    input logic CLK_IN1,
    input logic CLK_OUT,
    input logic [1:0] counter,
    input logic reset
);
    // Clock: CLK_IN1 posedge. Async reset: active-LOW 'reset' derived as (counter == 2'b11). Sequential logic.

    // 'reset' is exactly when counter is 2'b11.
    check_reset_definition: assert property (
        @(posedge CLK_IN1) reset == (counter == 2'b11)
    );

    // On any cycle, counter must be 2'b00 on the next rising edge.
    check_counter_next_zero: assert property (
        @(posedge CLK_IN1) 1'b1 |=> (counter == 2'b00)
    );

    // If reset is LOW at this edge, counter becomes 0 next cycle.
    check_counter_next_zero_when_reset_low: assert property (
        @(posedge CLK_IN1) (!reset) |=> (counter == 2'b00)
    );

    // If counter is 2'b11 at this edge, it becomes 0 next cycle.
    check_counter_wrap_from_3_to_0: assert property (
        @(posedge CLK_IN1) (counter == 2'b11) |=> (counter == 2'b00)
    );

    // When reset is LOW, CLK_OUT is forced LOW on the next cycle.
    check_clk_out_forced_low: assert property (
        @(posedge CLK_IN1) (!reset) |=> (CLK_OUT == 1'b0)
    );

    // When reset is HIGH (counter==3), CLK_OUT holds its previous value into the next cycle.
    check_clk_out_stable_when_reset_high: assert property (
        @(posedge CLK_IN1) reset |=> (CLK_OUT == $past(CLK_OUT))
    );

    // If previous cycle had reset LOW, CLK_OUT must be LOW now.
    check_clk_out_low_after_prev_reset_low: assert property (
        @(posedge CLK_IN1) $past(!reset) |-> (CLK_OUT == 1'b0)
    );

    // Counter==0 implies reset is LOW in the same cycle.
    check_reset_low_when_counter_zero: assert property (
        @(posedge CLK_IN1) (counter == 2'b00) |-> (reset == 1'b0)
    );

    // reset cannot remain HIGH for two consecutive sampled cycles.
    check_reset_single_cycle_pulse: assert property (
        @(posedge CLK_IN1) reset |=> !reset
    );

    // Once reset is LOW, it remains LOW on the next sampled cycle.
    check_reset_stays_low: assert property (
        @(posedge CLK_IN1) !reset |=> !reset
    );
endmodule