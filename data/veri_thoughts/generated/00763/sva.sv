module counter_with_load_reset_sva (
    input  logic [3:0] DATA_IN,
    input  logic       LOAD,
    input  logic       CLK,
    input  logic       RESET,
    input  logic [3:0] COUNT
);
    ///// Reset behavior /////
    // When RESET is asserted low, COUNT must be 0.
    check_reset_drives_zero: assert property (
        @(posedge CLK) (!RESET) |-> (COUNT == 4'd0)
    );

    ///// Next-state behavior /////
    // General next-state: after a non-reset cycle, COUNT matches LOAD/Data/Inc from previous cycle.
    check_next_state_function: assert property (
        @(posedge CLK) disable iff (!RESET)
            $past(RESET) |-> COUNT == ($past(LOAD) ? $past(DATA_IN) : (($past(COUNT) + 4'd1) & 4'hF))
    );

    // LOAD=1 loads DATA_IN on the next cycle.
    check_load_updates_next: assert property (
        @(posedge CLK) disable iff (!RESET)
            $past(RESET) && $past(LOAD) |-> (COUNT == $past(DATA_IN))
    );

    // LOAD=0 increments COUNT by 1 modulo 16 on the next cycle.
    check_increment_updates_next: assert property (
        @(posedge CLK) disable iff (!RESET)
            $past(RESET) && !$past(LOAD) |-> (COUNT == (($past(COUNT) + 4'd1) & 4'hF))
    );

    // LOAD=0 causes COUNT to change (it cannot hold its value).
    check_increment_changes_value: assert property (
        @(posedge CLK) disable iff (!RESET)
            $past(RESET) && !$past(LOAD) |-> (COUNT != $past(COUNT))
    );

    // With LOAD=0 and COUNT at 15, next COUNT wraps to 0.
    check_wrap_on_max_no_load: assert property (
        @(posedge CLK) disable iff (!RESET)
            $past(RESET) && !$past(LOAD) && ($past(COUNT) == 4'hF) |-> (COUNT == 4'h0)
    );

    // If LOAD=1, the load path has priority over increment (distinct from +1 result).
    check_load_priority_over_increment: assert property (
        @(posedge CLK) disable iff (!RESET)
            $past(RESET) && $past(LOAD) &&
            ($past(DATA_IN) != (($past(COUNT) + 4'd1) & 4'hF)) |-> (COUNT != (($past(COUNT) + 4'd1) & 4'hF))
    );

    // Two consecutive cycles with LOAD=0 increment COUNT by 2 modulo 16.
    check_two_cycle_increment_no_load: assert property (
        @(posedge CLK) disable iff (!RESET)
            $past(RESET,2) && $past(RESET) && !$past(LOAD,2) && !$past(LOAD)
            |-> COUNT == (($past(COUNT,2) + 4'd2) & 4'hF)
    );

    // LOAD followed by no LOAD results in DATA_IN+1 on the second cycle (modulo 16).
    check_load_then_increment: assert property (
        @(posedge CLK) disable iff (!RESET)
            $past(RESET,2) && $past(RESET) && $past(LOAD,2) && !$past(LOAD)
            |-> COUNT == (($past(DATA_IN,2) + 4'd1) & 4'hF)
    );
endmodule