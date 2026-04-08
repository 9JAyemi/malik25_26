module debounce_sva (
    input logic clk,
    input logic PB,
    input logic PB_state,
    input logic init_state,
    input logic [11:0] PB_cnt
);

    // A new idle input change captures PB, starts counting, and leaves the output unchanged.
    check_start_on_input_change: assert property (
        @(posedge clk)
        (PB_cnt == 12'd0 && PB != init_state)
        |=> (PB_cnt == 12'd1 &&
             init_state == $past(PB) &&
             PB_state == $past(PB_state))
    );

    // When idle and unchanged, all stored state holds.
    check_idle_holds_state: assert property (
        @(posedge clk)
        (PB_cnt == 12'd0 && PB == init_state)
        |=> (PB_cnt == 12'd0 &&
             init_state == $past(init_state) &&
             PB_state == $past(PB_state))
    );

    // During an active debounce interval, the counter increments and state holds.
    check_active_count_progress: assert property (
        @(posedge clk)
        (PB_cnt != 12'd0 && PB_cnt != 12'hfff)
        |=> (PB_cnt == ($past(PB_cnt) + 12'd1) &&
             init_state == $past(init_state) &&
             PB_state == $past(PB_state))
    );

    // Terminal count updates the debounced output and clears the counter.
    check_complete_on_terminal_count: assert property (
        @(posedge clk)
        (PB_cnt == 12'hfff)
        |=> (PB_cnt == 12'd0 &&
             PB_state == $past(init_state) &&
             init_state == $past(init_state))
    );

    // A visible count of one only comes from a new idle-to-active transition.
    check_count_one_only_after_start: assert property (
        @(posedge clk)
        (!$initstate && PB_cnt == 12'd1)
        |-> (($past(PB_cnt) == 12'd0) &&
             ($past(PB) != $past(init_state)))
    );

    // init_state only changes when an idle input change was detected.
    check_init_state_changes_only_on_start: assert property (
        @(posedge clk)
        (!$initstate && $changed(init_state))
        |-> (($past(PB_cnt) == 12'd0) &&
             ($past(PB) != $past(init_state)))
    );

    // PB_state only changes after the counter was at terminal count.
    check_output_changes_only_on_completion: assert property (
        @(posedge clk)
        (!$initstate && $changed(PB_state))
        |-> ($past(PB_cnt) == 12'hfff)
    );

    // Any PB_state change matches the previously captured input and a cleared counter.
    check_output_change_value_and_clear: assert property (
        @(posedge clk)
        (!$initstate && $changed(PB_state))
        |-> (PB_state == $past(init_state) &&
             PB_cnt == 12'd0)
    );

    // The counter only clears from a nonzero value when completion occurs.
    check_counter_clears_only_on_completion: assert property (
        @(posedge clk)
        (!$initstate && ($past(PB_cnt) != 12'd0) && PB_cnt == 12'd0)
        |-> ($past(PB_cnt) == 12'hfff)
    );

endmodule