module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] out
);
    // Synchronous reset drives out to zero on the same clock.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (out == 4'b0000)
    );

    // While reset remains asserted across cycles, out stays at zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) reset && $past(reset) |-> (out == 4'b0000)
    );

    // When not in reset, out increments by one each cycle (modulo 16).
    check_increment_each_cycle: assert property (
        @(posedge clk) disable iff (reset) out == $past(out) + 4'd1
    );

    // Wrap from 0xF to 0x0 on the next non-reset cycle.
    check_wraparound_from_F_to_0: assert property (
        @(posedge clk) disable iff (reset) ($past(out) == 4'hF) |-> (out == 4'h0)
    );

    // Out must change every non-reset cycle.
    check_output_changes_each_tick: assert property (
        @(posedge clk) disable iff (reset) out != $past(out)
    );

    // On the cycle reset deasserts, out becomes 1.
    check_deassert_goes_to_one: assert property (
        @(posedge clk) $fell(reset) |-> (out == 4'd1)
    );

    // On reset deassertion, previous out was 0.
    check_prev_zero_before_deassert: assert property (
        @(posedge clk) $fell(reset) |-> ($past(out) == 4'd0)
    );
endmodule