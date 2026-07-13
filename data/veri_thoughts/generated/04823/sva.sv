module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [3:0] count
);

    // Reset drives the counter to zero.
    check_count_zero_on_reset: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // An enabled cycle increments the counter by one modulo 16.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        en |=> (count == ($past(count) + 4'd1))
    );

    // A disabled cycle holds the counter value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        !en |=> (count == $past(count))
    );

endmodule