module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // When reset is asserted, count must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 4'h0)
    );

    // If reset is high in consecutive cycles, count holds at 0.
    check_reset_holds_zero: assert property (
        @(posedge clk) (($past(rst)===1'b1) && rst) |-> (count == 4'h0) && (count == $past(count))
    );

    // If previous cycle was in reset, that previous count must have been 0.
    check_prev_reset_count_zero: assert property (
        @(posedge clk) (($past(rst)===1'b1) && !rst) |-> ($past(count) == 4'h0)
    );

    // On the first cycle after reset deasserts, counter increments from the previous value.
    check_increment_after_reset_release: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == $past(count) + 1)
    );

    // With reset deasserted for two consecutive cycles, counter increments by 1.
    check_increment_when_running: assert property (
        @(posedge clk) disable iff (rst) (!rst && ($past(rst)===1'b0)) |-> (count == $past(count) + 1)
    );

    // Wrap-around: from 0xF to 0x0 when running.
    check_wraparound_mod16: assert property (
        @(posedge clk) disable iff (rst) (!rst && ($past(rst)===1'b0) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // LSB toggles every cycle when running.
    check_lsb_toggles_when_running: assert property (
        @(posedge clk) disable iff (rst) (!rst && ($past(rst)===1'b0)) |-> (count[0] == ~$past(count[0]))
    );
endmodule