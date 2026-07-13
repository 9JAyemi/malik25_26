module fourBitCounter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Reset clears the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'h0)
    );

    // When below 15, the counter increments by one.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'hF) |=> (count == ($past(count) + 4'h1))
    );

    // A count of 15 wraps back to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'hF) |=> (count == 4'h0)
    );

    // Zero advances to one when reset is low.
    check_zero_advances_to_one: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'h0) |=> (count == 4'h1)
    );

    // Fourteen advances to fifteen when reset is low.
    check_fourteen_advances_to_fifteen: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'hE) |=> (count == 4'hF)
    );

endmodule