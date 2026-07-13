module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] q
);
    // On each falling edge (from 2nd onward), q equals d from the prior falling edge.
    check_q_matches_prev_d_on_negedge: assert property (
        @(negedge clk) $past(1'b1) |-> (q == $past(d))
    );

    // If d is unchanged across the last two falling edges, q is unchanged now.
    check_stable_input_implies_stable_q: assert property (
        @(negedge clk) ($past(1'b1) && $past(1'b1,2) && ($past(d) == $past(d,2))) |-> (q == $past(q))
    );

    // If d changed between the last two falling edges, q must change now.
    check_input_toggle_implies_q_toggle: assert property (
        @(negedge clk) ($past(1'b1) && $past(1'b1,2) && ($past(d) != $past(d,2))) |-> (q != $past(q))
    );
endmodule