module johnson_counter_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] out
);

    // Reset forces the counter output to zero.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |-> (out == 3'b000)
    );

    // The first cycle after reset release still shows the reset value.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (out == 3'b000)
    );

    // The counter follows the Johnson shift rule on each active cycle.
    check_shift_rule: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (out == { $past(out[1:0]), $past(out[2]) })
    );

    // Bit 0 takes the previous value of bit 1.
    check_bit0_shifts_from_bit1: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (out[0] == $past(out[1]))
    );

    // Bit 1 takes the previous value of bit 2.
    check_bit1_shifts_from_bit2: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (out[1] == $past(out[2]))
    );

    // Bit 2 takes the previous value of bit 0.
    check_bit2_shifts_from_bit0: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (out[2] == $past(out[0]))
    );

    // The full output vector follows the Johnson shift rule.
    check_vector_shift_rule: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |-> (out == { $past(out[1:0]), $past(out[2]) })
    );

    // The output repeats every three active cycles.
    check_periodicity_three: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset,1) && !$past(reset,2) && !$past(reset,3)) |-> (out == $past(out,3))
    );

endmodule