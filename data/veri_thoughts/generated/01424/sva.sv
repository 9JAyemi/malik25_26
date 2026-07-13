module example004_sva (
    input logic clk,
    input logic rst,
    input logic y,
    input logic [3:0] counter
);
    // y reflects (counter == 12)
    check_y_matches_counter_eq12: assert property (
        @(posedge clk) disable iff (rst) (y == (counter == 4'd12))
    );

    // On reset assertion, next counter is 0
    check_reset_drives_counter_zero_next: assert property (
        @(posedge clk) rst |-> ##1 (counter == 4'd0)
    );

    // While reset is held HIGH across consecutive cycles, counter stays 0
    check_hold_zero_while_reset: assert property (
        @(posedge clk) rst && $past(rst) |-> (counter == 4'd0)
    );

    // When not in reset and counter != 9, next is either reset asserted or counter increments by 1
    check_increment_or_reset: assert property (
        @(posedge clk) disable iff (rst) (counter != 4'd9) |-> ##1 (rst || (counter == $past(counter) + 4'd1))
    );

    // When not in reset and counter is 9, next counter is 0
    check_wrap_on_nine: assert property (
        @(posedge clk) disable iff (rst) (counter == 4'd9) |-> ##1 (counter == 4'd0)
    );

    // y cannot be HIGH in two consecutive cycles (counter advances)
    check_y_not_sticky: assert property (
        @(posedge clk) disable iff (rst) y |-> ##1 !y
    );

    // When not in reset and counter is 15, next counter wraps to 0 (4-bit increment)
    check_wrap_on_fifteen: assert property (
        @(posedge clk) disable iff (rst) (counter == 4'd15) |-> ##1 (counter == 4'd0)
    );

    // On reset assertion, next y is 0 (since counter becomes 0)
    check_reset_drives_y_zero_next: assert property (
        @(posedge clk) rst |-> ##1 (y == 1'b0)
    );
endmodule