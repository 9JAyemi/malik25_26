module clock_divider_sva (
    input logic        clk_50,
    input logic        clk_1,
    input logic [31:0] counter
);

    // Counter increments by one when it is not at the terminal count.
    check_counter_increments: assert property (
        @(posedge clk_50)
        (counter != 32'd50000000) |=> (counter == ($past(counter) + 32'd1))
    );

    // Counter resets to zero after reaching the terminal count.
    check_counter_wraps_to_zero: assert property (
        @(posedge clk_50)
        (counter == 32'd50000000) |=> (counter == 32'd0)
    );

    // clk_1 toggles after the terminal count is reached.
    check_clk1_toggles_on_terminal_count: assert property (
        @(posedge clk_50)
        (counter == 32'd50000000) |=> (clk_1 === ~$past(clk_1))
    );

    // clk_1 holds its value when the counter is not at the terminal count.
    check_clk1_holds_when_not_terminal: assert property (
        @(posedge clk_50)
        (counter != 32'd50000000) |=> (clk_1 === $past(clk_1))
    );

endmodule