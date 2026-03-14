module ring_counter_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] out
);
    // On previous-cycle reset, out must be zero now.
    check_reset_clears_next: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (out == 3'b000)
    );

    // When not in reset, current out equals left-rotate of prior out.
    check_rotate_update: assert property (
        @(posedge clk) disable iff (reset) !reset |-> (out == {$past(out[1:0]), $past(out[2])})
    );

    // When not in reset on consecutive cycles, bit0 equals prior bit2.
    check_rotate_bit0: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && !reset |-> (out[0] == $past(out[2]))
    );

    // When not in reset on consecutive cycles, bit1 equals prior bit0.
    check_rotate_bit1: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && !reset |-> (out[1] == $past(out[0]))
    );

    // When not in reset on consecutive cycles, bit2 equals prior bit1.
    check_rotate_bit2: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && !reset |-> (out[2] == $past(out[1]))
    );

    // Zero value persists when not in reset (rotate(0) == 0).
    check_zero_sticks_no_reset: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && !reset && ($past(out) == 3'b000) |-> (out == 3'b000)
    );

    // After three cycles without reset, out returns to its value three cycles ago.
    check_three_cycle_period: assert property (
        @(posedge clk) disable iff (reset) !reset && $past(!reset) && $past(!reset,2) |-> (out == $past(out,3))
    );

    // After two cycles without reset, out equals out from two cycles ago rotated left by 2.
    check_two_step_rotate: assert property (
        @(posedge clk) disable iff (reset) !reset && $past(!reset) |-> (out == { $past(out[0],2), $past(out[2],2), $past(out[1],2) })
    );

    // 111 is invariant under rotation when not in reset.
    check_rotate_111_stable: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && !reset && ($past(out) == 3'b111) |-> (out == 3'b111)
    );

    // Specific rotation example: 101 rotates to 011 when not in reset.
    check_rotate_101_to_011: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && !reset && ($past(out) == 3'b101) |-> (out == 3'b011)
    );
endmodule