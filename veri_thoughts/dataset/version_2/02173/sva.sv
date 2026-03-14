module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] q
);
    // Clock: clk (negedge); Reset: none. Sequential DFF: q captures d on each negedge.

    // q equals d from the previous negedge of clk.
    check_q_matches_prev_d: assert property (
        @(negedge clk) disable iff ($initstate) q == $past(d)
    );

    // If d changed between the last two negedges, q must change at this negedge.
    check_q_change_reflects_d_change: assert property (
        @(negedge clk) disable iff ($initstate)
            ($past(1'b1,2) && ($past(d) != $past(d,2))) |-> (q != $past(q))
    );

    // If d was stable across the last two negedges, q must be stable across them.
    check_q_stable_when_d_stable: assert property (
        @(negedge clk) disable iff ($initstate)
            ($past(1'b1,2) && ($past(d) == $past(d,2))) |-> (q == $past(q))
    );
endmodule