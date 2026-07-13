module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [15:0] sum
);
    // On any cycle reset is asserted, sum must be 0 in the next cycle.
    reset_clears_sum_next: assert property (
        @(posedge clk) reset |=> (sum == 16'h0000)
    );

    // While reset stays asserted across cycles, sum holds at 0.
    reset_holds_sum_zero_while_asserted: assert property (
        @(posedge clk) ($past(reset) && reset) |-> (sum == 16'h0000)
    );

    // On reset deassertion, the registered sum is still 0 from the prior reset cycle.
    reset_release_preserves_zero: assert property (
        @(posedge clk) $fell(reset) |-> (sum == 16'h0000)
    );

    // When not in reset now and last cycle, sum equals previous (a*b + zero-extended c).
    sum_matches_prev_calc: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (sum == $past( ((a * b) + {8'h00, c})[15:0] ))
    );

    // Low byte of sum matches low byte of previous cycle's calculation.
    sum_low_byte_matches_prev_calc: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (sum[7:0] == $past( ((a * b) + {8'h00, c})[7:0] ))
    );

    // High byte of sum matches high byte of previous cycle's calculation.
    sum_high_byte_matches_prev_calc: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (sum[15:8] == $past( ((a * b) + {8'h00, c})[15:8] ))
    );

    // If c was zero last cycle (and not in reset), sum equals previous a*b.
    sum_equals_prev_product_when_c_zero: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(c == 8'h00)) |-> (sum == $past(a * b))
    );

    // If a was zero last cycle (and not in reset), sum equals zero-extended previous c.
    sum_equals_prev_c_when_a_zero: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(a == 8'h00)) |-> (sum == $past({8'h00, c}))
    );

    // If b was zero last cycle (and not in reset), sum equals zero-extended previous c.
    sum_equals_prev_c_when_b_zero: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(b == 8'h00)) |-> (sum == $past({8'h00, c}))
    );

    // If a was 1 last cycle (and not in reset), sum equals previous (b + c) zero-extended.
    sum_equals_prev_b_plus_c_when_a_one: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(a == 8'h01)) |-> (sum == $past( ({8'h00, b} + {8'h00, c})[15:0] ))
    );

    // If b was 1 last cycle (and not in reset), sum equals previous (a + c) zero-extended.
    sum_equals_prev_a_plus_c_when_b_one: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(b == 8'h01)) |-> (sum == $past( ({8'h00, a} + {8'h00, c})[15:0] ))
    );

    // With two prior non-reset cycles and stable inputs, sum is stable across the last two cycles.
    sum_stable_when_inputs_stable_two_cycles: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset,1) && $past(!reset,2) &&
             ($past(a,1) == $past(a,2)) &&
             ($past(b,1) == $past(b,2)) &&
             ($past(c,1) == $past(c,2)))
            |-> (sum == $past(sum))
    );
endmodule