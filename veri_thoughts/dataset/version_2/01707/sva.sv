module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] q
);
    ///// Functional relation between q and d /////
    // q equals d sampled on the previous negedge of clk (1-cycle latency).
    check_q_delayed_by_one_cycle: assert property (
        @(negedge clk) 1'b1 |-> ##1 (q == $past(d))
    );

    // If d is stable between negedges, q stays stable over the next interval.
    check_q_stable_when_d_stable: assert property (
        @(negedge clk) $stable(d) |-> ##1 $stable(q)
    );

    // Any change on d across negedges causes a change on q one cycle later.
    check_q_changes_follow_d_changes: assert property (
        @(negedge clk) $changed(d) |-> ##1 $changed(q)
    );

    // If q changes at a negedge, d must have changed in the prior cycle.
    check_q_change_implies_prior_d_change: assert property (
        @(negedge clk) $changed(q) |-> $past($changed(d))
    );

    ///// Bitwise edge propagation /////
    genvar i;
    for (i = 0; i < 8; i++) begin : gen_edge_prop
        // A rising edge on d[i] appears on q[i] one negedge later.
        check_rise_propagates: assert property (
            @(negedge clk) $rose(d[i]) |-> ##1 $rose(q[i])
        );
        // A falling edge on d[i] appears on q[i] one negedge later.
        check_fall_propagates: assert property (
            @(negedge clk) $fell(d[i]) |-> ##1 $fell(q[i])
        );
        // A rise on q[i] implies a rise on d[i] in the prior cycle.
        check_q_rise_implies_prior_d_rise: assert property (
            @(negedge clk) $rose(q[i]) |-> $past($rose(d[i]))
        );
        // A fall on q[i] implies a fall on d[i] in the prior cycle.
        check_q_fall_implies_prior_d_fall: assert property (
            @(negedge clk) $fell(q[i]) |-> $past($fell(d[i]))
        );
    end
endmodule