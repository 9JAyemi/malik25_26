module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       ctrl,
    input logic [7:0] max_val,
    input logic [7:0] min_val,
    input logic [7:0] count
);

    // Reset holds count at zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 8'd0)
    );

    // Up-counting below max increments by one.
    check_up_count_increment: assert property (
        @(posedge clk) disable iff (rst)
        (ctrl && (count != max_val)) |=> (count == ($past(count) + 8'd1))
    );

    // Up-counting at max wraps to zero.
    check_up_count_wrap_zero: assert property (
        @(posedge clk) disable iff (rst)
        (ctrl && (count == max_val)) |=> (count == 8'd0)
    );

    // Down-counting above min decrements by one.
    check_down_count_decrement: assert property (
        @(posedge clk) disable iff (rst)
        ((!ctrl) && (count != min_val)) |=> (count == ($past(count) - 8'd1))
    );

    // Down-counting at min reloads max_val.
    check_down_count_wrap_max: assert property (
        @(posedge clk) disable iff (rst)
        ((!ctrl) && (count == min_val)) |=> (count == $past(max_val))
    );

endmodule