module johnson_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [2:0] count
);

    // A sampled reset must leave count at 000 on the next clock.
    check_reset_clears_count_next_cycle: assert property (
        @(posedge clk) reset |=> (count == 3'b000)
    );

    // At the sampled clock where reset deasserts, count is still 000.
    check_release_cycle_count_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (count == 3'b000)
    );

    // One clock after reset deassertion, count remains 000.
    check_release_plus1_count_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> (count == 3'b000)
    );

    // Two clocks after reset deassertion, count is still 000.
    check_release_plus2_count_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##1 (count == 3'b000)
    );

    // Three clocks after reset deassertion, count becomes 111.
    check_release_plus3_count_ones: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##2 (count == 3'b111)
    );

    // Four clocks after reset deassertion, count remains 111.
    check_release_plus4_count_ones: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##3 (count == 3'b111)
    );

    // Five clocks after reset deassertion, count returns to 000.
    check_release_plus5_count_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##4 (count == 3'b000)
    );

    // Six clocks after reset deassertion, count remains 000.
    check_release_plus6_count_zero: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##5 (count == 3'b000)
    );

    // Seven clocks after reset deassertion, count becomes 111 again.
    check_release_plus7_count_ones: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##6 (count == 3'b111)
    );

    // Eight clocks after reset deassertion, count remains 111.
    check_release_plus8_count_ones: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> ##7 (count == 3'b111)
    );

endmodule