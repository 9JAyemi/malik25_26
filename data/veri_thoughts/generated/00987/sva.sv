module up_down_counter_sva (
    input logic clk,
    input logic rst,
    input logic up_down,
    input logic [3:0] count
);
    ///// Reset behavior /////
    // On any clock where rst is HIGH, count must be 0.
    check_reset_sets_zero: assert property (
        @(posedge clk) rst |-> (count == 4'b0000)
    );

    // On the cycle rst deasserts, count remains 0 (was set by prior cycle).
    check_count_zero_on_reset_fall: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'b0000)
    );

    ///// Up/Down counting /////
    // With rst LOW and up_down HIGH, next count = current + 1 (mod 16).
    check_increment_on_up: assert property (
        @(posedge clk) disable iff (rst) up_down |-> ##1 (count == ($past(count) + 4'b0001))
    );

    // With rst LOW and up_down LOW, next count = current - 1 (mod 16).
    check_decrement_on_down: assert property (
        @(posedge clk) disable iff (rst) !up_down |-> ##1 (count == ($past(count) - 4'b0001))
    );

    // Increment wrap: at 0xF with up_down HIGH, next count wraps to 0x0.
    check_wrap_inc_from_max: assert property (
        @(posedge clk) disable iff (rst) (up_down && (count == 4'hF)) |-> ##1 (count == 4'h0)
    );

    // Decrement wrap: at 0x0 with up_down LOW, next count wraps to 0xF.
    check_wrap_dec_from_min: assert property (
        @(posedge clk) disable iff (rst) (!up_down && (count == 4'h0)) |-> ##1 (count == 4'hF)
    );
endmodule