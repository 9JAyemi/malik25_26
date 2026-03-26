module up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Reset clears the counter to zero by the next clock sample.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // When enabled outside reset, count increments by one modulo 16.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 4'b0001))
    );

    // When disabled outside reset, count holds its previous value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // Enabling at the maximum value wraps the counter to zero.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'hf)) |=> (count == 4'h0)
    );

endmodule