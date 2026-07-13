module bcd_ctr_sva (
    input logic       clk,
    input logic       en,
    input logic       ar,
    input logic [3:0] dig1,
    input logic [3:0] dig2,
    input logic [3:0] dig3
);

    // One clock after reset was sampled low, all digits are still zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (!ar)
        (($past(ar) === 1'b0)) |-> ((dig1 == 4'd0) && (dig2 == 4'd0) && (dig3 == 4'd0))
    );

    // From a valid BCD state, the next state also stays within BCD range.
    check_bcd_range_preserved: assert property (
        @(posedge clk) disable iff (!ar)
        ((dig1 <= 4'd9) && (dig2 <= 4'd9) && (dig3 <= 4'd9))
        |=> ((dig1 <= 4'd9) && (dig2 <= 4'd9) && (dig3 <= 4'd9))
    );

    // When enable is low, the counter holds its state.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!ar)
        (!en)
        |=> ((dig1 == $past(dig1)) && (dig2 == $past(dig2)) && (dig3 == $past(dig3)))
    );

    // When the count is 999 and enable is high, the counter saturates.
    check_hold_at_999: assert property (
        @(posedge clk) disable iff (!ar)
        (en && (dig1 == 4'd9) && (dig2 == 4'd9) && (dig3 == 4'd9))
        |=> ((dig1 == 4'd9) && (dig2 == 4'd9) && (dig3 == 4'd9))
    );

    // With no ones-digit carry, only dig1 increments.
    check_increment_ones_digit: assert property (
        @(posedge clk) disable iff (!ar)
        (en && (dig1 <= 4'd8) && (dig2 <= 4'd9) && (dig3 <= 4'd9))
        |=> ((dig1 == ($past(dig1) + 4'd1)) &&
             (dig2 ==  $past(dig2)) &&
             (dig3 ==  $past(dig3)))
    );

    // A ones-digit carry increments dig2 and clears dig1.
    check_carry_ones_to_tens: assert property (
        @(posedge clk) disable iff (!ar)
        (en && (dig1 == 4'd9) && (dig2 <= 4'd8) && (dig3 <= 4'd9))
        |=> ((dig1 == 4'd0) &&
             (dig2 == ($past(dig2) + 4'd1)) &&
             (dig3 ==  $past(dig3)))
    );

    // A tens-digit carry increments dig3 and clears dig2 and dig1.
    check_carry_tens_to_hundreds: assert property (
        @(posedge clk) disable iff (!ar)
        (en && (dig1 == 4'd9) && (dig2 == 4'd9) && (dig3 <= 4'd8))
        |=> ((dig1 == 4'd0) &&
             (dig2 == 4'd0) &&
             (dig3 == ($past(dig3) + 4'd1)))
    );

endmodule