module binary_counter_sva(
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // A reset seen on one clock leaves count at zero on the next clock.
    check_reset_drives_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(rst) |-> (count == 4'h0)
    );

    // A sampled 15 wraps to zero on the following clock when reset was low.
    check_wrap_from_fifteen: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // Counts below 15 either increment or get cleared by an async reset pulse.
    check_increment_or_async_clear: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(count) != 4'hF)) |-> ((count == 4'h0) || (count == ($past(count) + 4'h1)))
    );

    // Any nonzero count must come from the previous value plus one.
    check_nonzero_has_linear_predecessor: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count != 4'h0) |-> (!$past(rst) && ($past(count) == (count - 4'h1)))
    );

endmodule