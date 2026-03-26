module up_down_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       dir,
    input logic [3:0] count
);

    // A low reset drives count to zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk)
        !rst |=> (count == 4'h0)
    );

    // If reset stays low, count remains zero.
    check_reset_holds_count_zero: assert property (
        @(posedge clk)
        (!rst && $past(!rst)) |-> (count == 4'h0)
    );

    // Counting up increments by one when not at the maximum.
    check_increment_from_non_max: assert property (
        @(posedge clk) disable iff (!rst)
        (dir && (count != 4'hF)) |=> (count == ($past(count) + 4'd1))
    );

    // Counting up wraps from 4'hF to 4'h0.
    check_increment_wrap_from_max: assert property (
        @(posedge clk) disable iff (!rst)
        (dir && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Counting down decrements by one when not at zero.
    check_decrement_from_non_zero: assert property (
        @(posedge clk) disable iff (!rst)
        (!dir && (count != 4'h0)) |=> (count == ($past(count) - 4'd1))
    );

    // Counting down wraps from 4'h0 to 4'hF.
    check_decrement_wrap_from_zero: assert property (
        @(posedge clk) disable iff (!rst)
        (!dir && (count == 4'h0)) |=> (count == 4'hF)
    );

endmodule