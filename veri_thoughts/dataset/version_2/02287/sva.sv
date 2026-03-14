module dffs_37_sva (
    input logic        clk,
    input logic        set,
    input logic [36:0] d,
    input logic [36:0] q
);
    // Clock: clk. No explicit reset. Sequential FF array with synchronous set to all 1s.

    // Synchronous set forces q to all 1s on the next cycle.
    check_set_forces_ones: assert property (
        @(posedge clk) set |=> (q == {37{1'b1}})
    );

    // With set deasserted, q loads d on the next cycle.
    check_no_set_loads_d: assert property (
        @(posedge clk) (!set && $past(1'b1)) |=> (q == $past(d))
    );

    // Next-state function: q equals prior set ? all 1s : prior d.
    check_next_q_matches_prev_inputs: assert property (
        @(posedge clk) $past(1'b1) |-> (q == ($past(set) ? {37{1'b1}} : $past(d)))
    );

    // If set stays low and d is stable across a cycle, q stays stable one cycle later.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) (!set) ##1 (!set && $stable(d)) |-> ##1 $stable(q)
    );

    // A set pulse followed by clear loads d from the clear cycle.
    check_set_pulse_then_clear_loads_d: assert property (
        @(posedge clk) set ##1 !set |-> ##1 (q == $past(d))
    );

    // When set stays low for two cycles and d changes, q changes one cycle later.
    check_d_change_propagates_with_latency: assert property (
        @(posedge clk) !set ##1 (!set && (d != $past(d))) |-> ##1 (q != $past(q))
    );
endmodule