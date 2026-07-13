module counter_sva (
    input logic clk,
    input logic reset,
    input logic [1:0] count
);

    // After a reset cycle, count must be zero.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (count == 2'b00)
    );

    // From 0, the counter increments to 1 when not coming out of reset.
    check_count_0_to_1: assert property (
        @(posedge clk) disable iff ($initstate || $past(reset))
        ($past(count) == 2'b00) |-> (count == 2'b01)
    );

    // From 1, the counter increments to 2 when not coming out of reset.
    check_count_1_to_2: assert property (
        @(posedge clk) disable iff ($initstate || $past(reset))
        ($past(count) == 2'b01) |-> (count == 2'b10)
    );

    // From 2, the counter increments to 3 when not coming out of reset.
    check_count_2_to_3: assert property (
        @(posedge clk) disable iff ($initstate || $past(reset))
        ($past(count) == 2'b10) |-> (count == 2'b11)
    );

    // From 3, the counter wraps back to 0 when not coming out of reset.
    check_count_3_to_0: assert property (
        @(posedge clk) disable iff ($initstate || $past(reset))
        ($past(count) == 2'b11) |-> (count == 2'b00)
    );

endmodule