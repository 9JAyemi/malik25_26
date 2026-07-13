module arriaiigz_ram_pulse_generator_sva (
    input logic clk,
    input logic ena,
    input logic pulse,
    input logic cycle
);

    ///// cycle (delayed clock) behavior /////
    // After every clk rising edge, cycle must be HIGH on the next clk edge.
    check_cycle_next_is_one: assert property (
        @(posedge clk) 1'b1 |=> (cycle == 1'b1)
    );

    // Once cycle is HIGH, it must remain HIGH on subsequent clk edges.
    check_cycle_stays_high: assert property (
        @(posedge clk) cycle |=> cycle
    );

    // cycle can have at most one rising edge in the whole run.
    check_cycle_rises_once: assert property (
        @(posedge clk) $rose(cycle) |-> (! $rose(cycle)) [*1:$]
    );

    ///// pulse update behavior /////
    // On each clk edge, pulse follows this next-state rule: if cycle rose in the last interval, capture ena; else hold value.
    check_pulse_update_rule: assert property (
        @(posedge clk) 1'b1 |=> (pulse == ($rose(cycle) ? $past(ena) : $past(pulse)))
    );

    // pulse may only change value in intervals where cycle had a rising edge.
    check_pulse_changes_only_on_cycle_rise: assert property (
        @(posedge clk) $changed(pulse) |-> $rose(cycle)
    );

    // If cycle did not rise in the last interval, pulse must be stable.
    check_pulse_stable_when_no_cycle_rise: assert property (
        @(posedge clk) !$rose(cycle) |-> $stable(pulse)
    );

endmodule