module up_counter_4bit_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] count
);

    ///// Reset behavior /////
    // When rst is LOW at a clock edge, count must be 0 in the same cycle.
    check_reset_clears_now: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == 4'b0000)
    );

    // When rst is LOW at a clock edge, count must be 0 at the next clock edge.
    check_reset_clears_next: assert property (
        @(posedge clk) (rst == 1'b0) |=> (count == 4'b0000)
    );

    // On a sampled rising edge of rst, count is 0 at that cycle.
    check_reset_release_sample_zero: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'b0000)
    );

    ///// Enable/Count behavior (active when rst is HIGH) /////
    // When enabled, count increments by 1 modulo 16 on the next cycle.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (rst == 1'b0) (en == 1'b1) |=> (count == ($past(count) + 4'h1))
    );

    // When enabled, count must change on the next cycle.
    check_change_when_enabled: assert property (
        @(posedge clk) disable iff (rst == 1'b0) (en == 1'b1) |=> (count != $past(count))
    );

    // When not enabled, count holds its value on the next cycle.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst == 1'b0) (en == 1'b0) |=> (count == $past(count))
    );

    // When enabled at 0xF, the next value wraps to 0x0.
    check_wrap_on_max: assert property (
        @(posedge clk) disable iff (rst == 1'b0) ((count == 4'hF) && (en == 1'b1)) |=> (count == 4'h0)
    );

endmodule