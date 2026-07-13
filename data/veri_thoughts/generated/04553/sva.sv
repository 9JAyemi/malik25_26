module counter_module_sva (
    input logic        clk,
    input logic        rst,
    input logic [31:0] count,
    input logic        max_reached
);

    // Synchronous reset clears the counter and flag on the next clock.
    check_reset_clears_state: assert property (
        @(posedge clk)
        rst |=> (count == 32'd0) && (max_reached == 1'b0)
    );

    // Below max, the counter increments by one and the flag stays low.
    check_increment_until_max: assert property (
        @(posedge clk) disable iff (rst)
        (count != 32'hFFFFFFFF) |=> (count == ($past(count) + 32'd1)) && (max_reached == 1'b0)
    );

    // At max, the counter saturates and the flag asserts.
    check_saturate_and_flag_at_max: assert property (
        @(posedge clk) disable iff (rst)
        (count == 32'hFFFFFFFF) |=> (count == $past(count)) && (max_reached == 1'b1)
    );

endmodule