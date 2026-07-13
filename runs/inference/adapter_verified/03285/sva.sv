module johnson_counter_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] out
);

// Reset drives the counter to 000 on the next clock.
    check_reset_clears_to_zero: assert property (
        @(posedge clk) reset |=> (out == 3'b000)
    );

// With reset low, the counter rotates left by one bit.
    check_rotate_left_when_not_reset: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out == {$past(out[1:0]), $past(out[2])})
    );

// Bit 0 takes the previous value of bit 1.
    check_bit0_from_bit1: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out[0] == $past(out[1]))
    );

// Bit 1 takes the previous value of bit 2.
    check_bit1_from_bit2: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out[1] == $past(out[2]))
    );

// Bit 2 takes the previous value of bit 0.
    check_bit2_from_bit0: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out[2] == $past(out[0]))
    );

// The full 3-bit vector rotates left by one bit.
    check_vector_rotate_left: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out == {$past(out[1:0]), $past(out[2])})
    );

endmodule
