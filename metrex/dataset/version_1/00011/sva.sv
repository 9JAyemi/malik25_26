module shift_reg_comp_sva (
    input logic clk,
    input logic reset,     // Active-high synchronous reset
    input logic load,
    input logic enable,
    input logic [3:0] data_in,
    input logic [3:0] out,
    // Internal combinational comparator output from the instantiated 'comparator' module
    input logic comp_out
);
    ////////////////////////////////////////////////////////////////////////////////
    // Analysis
    // - Clocks:       clk (posedge)
    // - Reset:        reset (active-high, synchronous)
    // - Logic type:   Mixed
    //   * Sequential: 'out' register updated on posedge clk with synchronous reset.
    //   * Combinational: 'comparator' outputs comp_out = (data_in == out).
    // - Key behaviors:
    //   * On reset, 'out' is cleared to 4'b0000 on the clock edge where reset is 1.
    //   * When load=1 (and reset=0), out updates to data_in on the next cycle.
    //   * When enable=1 and load=0 (and reset=0), out updates to data_in on the next cycle.
    //   * When load=0 and enable=0 (and reset=0), out holds its previous value.
    //   * comp_out always reflects equality between data_in and out combinationally.
    ////////////////////////////////////////////////////////////////////////////////

    ///// Comparator correctness /////
    // Comparator output must equal the equality of its inputs (data_in == out).
    comparator_function_correct: assert property (
        @(posedge clk) disable iff (reset) comp_out == (data_in == out)
    );

    ///// Reset behavior /////
    // On any clock where reset is asserted, out is cleared to zero (visible next cycle).
    reset_clears_out_next_cycle: assert property (
        @(posedge clk) reset |=> (out == 4'b0000)
    );

    ///// Load/Enable update rules /////
    // When load is asserted (and not reset), out updates to the data_in sampled on that edge.
    update_on_load: assert property (
        @(posedge clk) disable iff (reset) load |=> (out == $past(data_in))
    );

    // When enable is asserted without load (and not reset), out updates to the data_in sampled on that edge.
    update_on_enable_only: assert property (
        @(posedge clk) disable iff (reset) (!load && enable) |=> (out == $past(data_in))
    );

    // When both load and enable are asserted (and not reset), out still updates to data_in.
    update_when_both_load_and_enable: assert property (
        @(posedge clk) disable iff (reset) (load && enable) |=> (out == $past(data_in))
    );

    // When neither load nor enable is asserted (and not reset), out holds its previous value.
    hold_when_idle: assert property (
        @(posedge clk) disable iff (reset) (!load && !enable) |=> (out == $past(out))
    );

    ///// Change-causality /////
    // Any change in out between consecutive cycles must be caused by reset, load, or enable in the previous cycle.
    out_change_requires_previous_action: assert property (
        @(posedge clk) disable iff (reset) (out != $past(out)) |-> ($past(reset) || $past(load) || $past(enable))
    );

    ///// No-op update when data already matches /////
    // If an update is requested but data_in already equals out on that edge, the next-cycle out remains unchanged.
    update_with_same_data_no_effect: assert property (
        @(posedge clk) disable iff (reset) ((load || enable) && (data_in == out)) |=> (out == $past(out))
    );

    ///// Comparator stability /////
    // After an update (load or enable), if data_in remains stable into the next cycle, comparator must report equality.
    comp_out_high_after_update_with_stable_data: assert property (
        @(posedge clk) disable iff (reset) (load || enable) |=> ($stable(data_in) && (comp_out == 1'b1))
    );

    // If both comparator inputs (data_in and out) are stable across a cycle, its output must also be stable.
    comparator_stability_with_stable_inputs: assert property (
        @(posedge clk) disable iff (reset) ($stable(data_in) && $stable(out)) |-> $stable(comp_out)
    );

    ///// Reset hold /////
    // While reset remains asserted across consecutive cycles, out remains cleared (observably 0).
    out_held_zero_while_reset: assert property (
        @(posedge clk) reset && $past(reset) |-> (out == 4'b0000)
    );

endmodule