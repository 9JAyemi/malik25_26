module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum_output,
    input logic [7:0] product_output,
    input logic [7:0] difference_output
);

    // After a reset cycle, sum_output must be 0 on the next clock.
    reset_clears_sum_next: assert property (
        @(posedge clk) $past(reset) |-> (sum_output == 8'h00)
    );

    // After a reset cycle, product_output must be 0 on the next clock.
    reset_clears_product_next: assert property (
        @(posedge clk) $past(reset) |-> (product_output == 8'h00)
    );

    // After a reset cycle, difference_output must be 0 on the next clock.
    reset_clears_difference_next: assert property (
        @(posedge clk) $past(reset) |-> (difference_output == 8'h00)
    );

    // Adder: sum_output updates to a+b (mod 256) one cycle later when not in reset.
    adder_updates_from_inputs_onecycle: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (sum_output == (($past(a) + $past(b)) [7:0]))
    );

    // Multiplier: product_output updates to low 8 bits of a*b one cycle later when not in reset.
    multiplier_updates_from_inputs_low8_onecycle: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (product_output == (($past(a) * $past(b)) [7:0]))
    );

    // Difference: difference_output updates to prior (sum_output - product_output) when not in reset.
    difference_updates_from_regs_onecycle: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (difference_output == (($past(sum_output) - $past(product_output)) [7:0]))
    );

    // Pipeline composition: two-cycle relation from primary inputs to difference_output (no resets in the window).
    difference_two_cycle_from_primary_inputs: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(!reset,2)) |-> (
                difference_output == (
                    (($past(a,2) + $past(b,2)) [7:0]) - (($past(a,2) * $past(b,2)) [7:0])
                )
            )
    );

    // Adder stability: if a and b are unchanged over two cycles (no reset), sum_output holds its value.
    adder_stable_when_inputs_hold: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(!reset,2) &&
             ($past(a) == $past(a,2)) && ($past(b) == $past(b,2))) |-> (sum_output == $past(sum_output))
    );

    // Multiplier stability: if a and b are unchanged over two cycles (no reset), product_output holds its value.
    multiplier_stable_when_inputs_hold: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(!reset,2) &&
             ($past(a) == $past(a,2)) && ($past(b) == $past(b,2))) |-> (product_output == $past(product_output))
    );

    // Difference stability: if prior sum_output and product_output are unchanged over two cycles (no reset), difference_output holds.
    difference_stable_when_prev_regs_hold: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(!reset,2) &&
             ($past(sum_output) == $past(sum_output,2)) &&
             ($past(product_output) == $past(product_output,2))) |-> (difference_output == $past(difference_output))
    );

    // Algebraic check: (prior sum) equals (current difference + prior product) modulo 256 when not in reset.
    difference_linear_relation_prev_cycle: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> ((difference_output + $past(product_output)) [7:0] == $past(sum_output))
    );

endmodule