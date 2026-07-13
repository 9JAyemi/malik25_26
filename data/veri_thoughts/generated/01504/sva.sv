module dff_en_sva (
    input logic clk,
    input logic d,
    input logic en,
    input logic q,
    input logic q_bar
);
    // Clock: clk (posedge). Reset: none. Logic: FF with enable; q_bar is ~q.

    // q_bar is always the bitwise complement of q.
    check_qbar_complement: assert property (
        @(posedge clk) q_bar == ~q
    );

    // If en is LOW at a clock edge, then q(t) equals q(t-1) (hold behavior at that edge).
    check_hold_when_disabled: assert property (
        @(posedge clk) (!en) |-> (q == $past(q))
    );

    // If en is HIGH and d != q(t-1) at a clock edge, q changes at that edge.
    check_change_when_enabled_and_d_diff_qprev: assert property (
        @(posedge clk) (en && (d != q)) |-> (q != $past(q))
    );

    // If en is HIGH and d == q(t-1) at a clock edge, q does not change at that edge.
    check_nochange_when_enabled_and_d_eq_qprev: assert property (
        @(posedge clk) (en && (d == q)) |-> (q == $past(q))
    );

    // Any change on q must have been caused by prior en=1 and captures prior d.
    check_q_change_has_prior_enable_and_d: assert property (
        @(posedge clk) (q != $past(q)) |=> ($past(en) && (q == $past(d)))
    );

    // If q changes across a cycle, q_bar must also change (since q_bar == ~q).
    check_qbar_changes_with_q: assert property (
        @(posedge clk) (q != $past(q)) |-> (q_bar != $past(q_bar))
    );

    // If q_bar changes across a cycle, q must also change.
    check_q_changes_with_qbar: assert property (
        @(posedge clk) (q_bar != $past(q_bar)) |-> (q != $past(q))
    );
endmodule