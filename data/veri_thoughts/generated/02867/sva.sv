module up_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // On any clock where reset is asserted, count is driven to 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 4'b0000)
    );

    // When not in reset now and previously, count increments by 1.
    check_increment_when_no_reset: assert property (
        @(posedge clk) disable iff (rst) !$past(rst) |-> (count == $past(count) + 4'd1)
    );

    // First cycle after reset deasserts, count becomes 1.
    check_first_count_after_reset_release: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'd1)
    );

    // From 0xF, next value is 0 when not in reset.
    check_wrap_from_f_to_0_without_reset: assert property (
        @(posedge clk) disable iff (rst) ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // Over 2 consecutive cycles without reset, count increases by 2.
    check_two_cycle_increment_without_reset: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && !$past(rst,2)) |-> (count == $past(count,2) + 4'd2)
    );

    // Over 16 consecutive cycles without reset, count returns to the prior value.
    check_periodicity_16_without_reset: assert property (
        @(posedge clk) disable iff (rst) !rst[*16] |-> (count == $past(count,16))
    );
endmodule