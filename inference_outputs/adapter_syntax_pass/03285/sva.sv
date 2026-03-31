module johnson_counter_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] out
);

    // Reset forces the counter to 000 on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 3'b000)
    );

    // The first cycle after reset deassertion still shows 000.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (out == 3'b000)
    );

    // The next active cycle after reset deassertion shows 001.
    check_post_reset_first_increment: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> (out == 3'b001)
    );

    // The counter value is always one of the three Johnson states.
    check_out_is_johnson_state: assert property (
        @(posedge clk) disable iff (reset) (out inside {3'b000, 3'b001, 3'b010})
    );

    // 000 advances to 001 on the next active cycle.
    check_state_000_to_001: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b000) |=> (out == 3'b001)
    );

    // 001 advances to 010 on the next active cycle.
    check_state_001_to_010: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b001) |=> (out == 3'b010)
    );

    // 010 returns to 000 on the next active cycle.
    check_state_010_to_000: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b010) |=> (out == 3'b000)
    );

endmodule