module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [7:0] max_count,
    input logic [7:0] count
);

    // A sampled reset drives the counter to zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 8'd0)
    );

    // A reset held across clocks keeps the counter at zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) disable iff ($initstate) (rst && $past(rst)) |-> (count == 8'd0)
    );

    // When count matches max_count, the counter wraps to zero.
    check_wrap_on_max: assert property (
        @(posedge clk) disable iff (rst) (count == max_count) |=> (count == 8'd0)
    );

    // When count does not match max_count, the counter increments by one.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (rst) (count != max_count) |=> (count == ($past(count) + 8'd1))
    );

    // From zero with max_count at zero, the counter remains at zero.
    check_zero_max_stays_zero: assert property (
        @(posedge clk) disable iff (rst) (count == 8'd0 && max_count == 8'd0) |=> (count == 8'd0)
    );

    // From zero with a nonzero max_count, the counter advances to one.
    check_zero_count_advances_to_one: assert property (
        @(posedge clk) disable iff (rst) (count == 8'd0 && max_count != 8'd0) |=> (count == 8'd1)
    );

endmodule