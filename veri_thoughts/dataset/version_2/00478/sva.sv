module my_flip_flop_sva (
    input logic clk,
    input logic d,
    input logic rst,
    input logic q
);

    // q reflects the previous cycle's d when reset was not active.
    check_q_captures_previous_d: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) |-> (q == $past(d))
    );

    // A reset on the previous cycle forces q low.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (q == 1'b0)
    );

    // q holds its value when the previous d already matched q.
    check_q_holds_when_d_is_unchanged: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(d) == $past(q))) |-> (q == $past(q))
    );

    // q updates when the previous d differed from q.
    check_q_updates_when_d_changes: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(d) != $past(q))) |-> (q == $past(d))
    );

endmodule