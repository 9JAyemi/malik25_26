module dual_edge_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);
    // q reflects d=1 exactly 3 cycles later.
    propagate_d1_after_3: assert property (
        @(posedge clk) (d == 1'b1) |-> ##3 (q == 1'b1)
    );

    // q reflects d=0 exactly 3 cycles later.
    propagate_d0_after_3: assert property (
        @(posedge clk) (d == 1'b0) |-> ##3 (q == 1'b0)
    );

    // A rising edge on d appears on q after 3 cycles.
    rise_propagates_after_3: assert property (
        @(posedge clk) $rose(d) |-> ##3 $rose(q)
    );

    // A falling edge on d appears on q after 3 cycles.
    fall_propagates_after_3: assert property (
        @(posedge clk) $fell(d) |-> ##3 $fell(q)
    );

    // q equals d delayed by 3 cycles (after 3 cycles have elapsed).
    q_is_3cycle_delay_of_d: assert property (
        @(posedge clk) $past($past($past(1'b1))) |-> (q == $past(d,3))
    );

    // A change on q equals a change on d 3 cycles earlier.
    q_change_matches_d_change_3prior: assert property (
        @(posedge clk) $past($past($past($past(1'b1)))) |-> ($changed(q) == ($past(d,3) != $past(d,4)))
    );

    // A 1-cycle high pulse on d becomes a 1-cycle high pulse on q after 3 cycles.
    high_pulse_1cycle_replicates: assert property (
        @(posedge clk) ($rose(d) ##1 $fell(d)) |-> ##3 ($rose(q) ##1 $fell(q))
    );

    // A 1-cycle low pulse on d becomes a 1-cycle low pulse on q after 3 cycles.
    low_pulse_1cycle_replicates: assert property (
        @(posedge clk) ($fell(d) ##1 $rose(d)) |-> ##3 ($fell(q) ##1 $rose(q))
    );

    // If d is stable for 2 cycles, q is stable for 2 cycles starting 3 cycles later.
    stability_2cycles_replicates: assert property (
        @(posedge clk) $stable(d)[*2] |-> ##3 $stable(q)[*2]
    );

    // If d is stable for 3 cycles, q is stable for 3 cycles starting 3 cycles later.
    stability_3cycles_replicates: assert property (
        @(posedge clk) $stable(d)[*3] |-> ##3 $stable(q)[*3]
    );
endmodule