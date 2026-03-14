module counter_sva (
    input logic clk,
    input logic rst,       // active-high synchronous reset
    input logic en,
    input logic [3:0] count_out
);
    // Synchronous reset drives count_out to 0 on the next cycle.
    check_reset_clears_next: assert property (
        @(posedge clk) rst |=> (count_out == 4'd0)
    );

    // When previously enabled (and not in reset), counter increments by 1 modulo 16.
    check_increment_when_en_prev: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && $past(en) |-> (count_out == (($past(count_out) + 4'd1)[3:0]))
    );

    // When previously disabled (and not in reset), counter holds its value.
    check_hold_when_en0_prev: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && !$past(en) |-> (count_out == $past(count_out))
    );

    // A change from last cycle (without reset) implies previous enable was HIGH.
    check_change_implies_prev_en: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && (count_out != $past(count_out)) |-> $past(en)
    );

    // No change from last cycle (without reset) implies previous enable was LOW.
    check_no_change_implies_prev_not_en: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && (count_out == $past(count_out)) |-> !$past(en)
    );

    // When previously at 4'hF with enable, wraps to 0 on the next cycle.
    check_wrap_on_max: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && $past(en) && ($past(count_out) == 4'hF) |-> (count_out == 4'h0)
    );

    // Next-state equals prev_state plus prev_en modulo 16 (consolidated rule).
    check_one_step_function: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) |-> (count_out == (( $past(count_out) + ($past(en) ? 4'd1 : 4'd0) )[3:0]))
    );

    // If reset stays asserted across consecutive cycles, next cycle remains 0.
    check_reset_hold_zero_next: assert property (
        @(posedge clk) rst && $past(rst) |=> (count_out == 4'd0)
    );
endmodule