module shift_register_sva (
    input logic clk,
    input logic d,
    input logic shift,
    input logic q
);

    // q holds its value when shift is low.
    check_hold_when_shift_low: assert property (
        @(posedge clk) !shift |=> (q == $past(q))
    );

    // q can only change after a cycle with shift high.
    check_q_change_requires_shift: assert property (
        @(posedge clk) ((!$initstate) && (q != $past(q))) |-> $past(shift)
    );

    // A no-shift cycle followed by a shift moves that earlier d value to q.
    check_no_shift_then_shift_moves_d_to_q: assert property (
        @(posedge clk) (!shift ##1 shift) |=> (q == $past(d,2))
    );

    // Three consecutive shifts move d to q after three clocks.
    check_three_shifts_move_d_to_q: assert property (
        @(posedge clk) (shift ##1 shift ##1 shift) |=> (q == $past(d,3))
    );

endmodule