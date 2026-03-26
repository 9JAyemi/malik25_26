module up_counter_sva(
    input logic       clk,
    input logic       reset_n,
    input logic [2:0] count
);

    // Reset forces the counter to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) !reset_n |-> (count == 3'b000)
    );

    // A non-maximum count increments by one on the next clock.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (!reset_n)
        (count != 3'b111) |=> (count == ($past(count) + 3'b001))
    );

    // The maximum count wraps back to zero on the next clock.
    check_wrap_after_max: assert property (
        @(posedge clk) disable iff (!reset_n)
        (count == 3'b111) |=> (count == 3'b000)
    );

endmodule