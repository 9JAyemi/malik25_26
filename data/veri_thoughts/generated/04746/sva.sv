module updowncounterbehavioural_sva (
    input logic       in,
    input logic       clk,
    input logic       rst,
    input logic [3:0] out
);

    // Reset clears the counter to zero.
    check_reset_clears_counter: assert property (
        @(posedge clk) rst |=> (out == 4'b0000)
    );

    // A high input increments the counter by one.
    check_increment_when_in_high: assert property (
        @(posedge clk) disable iff (rst)
        (in == 1'b1) |=> (out == ($past(out) + 4'b0001))
    );

    // A low input decrements the counter by one.
    check_decrement_when_in_low: assert property (
        @(posedge clk) disable iff (rst)
        (in == 1'b0) |=> (out == ($past(out) - 4'b0001))
    );

    // Incrementing from 4'hF wraps the 4-bit counter to 0.
    check_increment_wraparound: assert property (
        @(posedge clk) disable iff (rst)
        ((in == 1'b1) && (out == 4'hF)) |=> (out == 4'h0)
    );

    // Decrementing from 0 wraps the 4-bit counter to 4'hF.
    check_decrement_wraparound: assert property (
        @(posedge clk) disable iff (rst)
        ((in == 1'b0) && (out == 4'h0)) |=> (out == 4'hF)
    );

endmodule