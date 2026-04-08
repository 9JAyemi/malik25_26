module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] count
);

    // Active-high reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'd0)
    );

    // From 0, the counter increments to 1.
    check_count_0_to_1: assert property (
        @(posedge clk) disable iff (reset) (count == 3'd0) |=> (count == 3'd1)
    );

    // From 1, the counter increments to 2.
    check_count_1_to_2: assert property (
        @(posedge clk) disable iff (reset) (count == 3'd1) |=> (count == 3'd2)
    );

    // From 2, the counter increments to 3.
    check_count_2_to_3: assert property (
        @(posedge clk) disable iff (reset) (count == 3'd2) |=> (count == 3'd3)
    );

    // From 3, the counter increments to 4.
    check_count_3_to_4: assert property (
        @(posedge clk) disable iff (reset) (count == 3'd3) |=> (count == 3'd4)
    );

    // From 4, the counter increments to 5.
    check_count_4_to_5: assert property (
        @(posedge clk) disable iff (reset) (count == 3'd4) |=> (count == 3'd5)
    );

    // From 5, the counter increments to 6.
    check_count_5_to_6: assert property (
        @(posedge clk) disable iff (reset) (count == 3'd5) |=> (count == 3'd6)
    );

    // From 6, the counter increments to 7.
    check_count_6_to_7: assert property (
        @(posedge clk) disable iff (reset) (count == 3'd6) |=> (count == 3'd7)
    );

    // From 7, the counter wraps back to 0.
    check_count_7_to_0: assert property (
        @(posedge clk) disable iff (reset) (count == 3'd7) |=> (count == 3'd0)
    );

endmodule