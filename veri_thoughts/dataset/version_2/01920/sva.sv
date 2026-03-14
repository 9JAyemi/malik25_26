module Divisor_Frecuencia_sva (
    input  logic        C_100Mhz,   // clock
    input  logic        C_1Hz,      // output from DUT
    input  logic [31:0] contador    // internal counter from DUT
);
    // Clock: C_100Mhz (posedge). No reset present in RTL.
    // Sequential logic: contador increments to LIMIT then toggles C_1Hz and clears.

    localparam int unsigned LIMIT = 32'd50000000 - 1;

    // Counter never exceeds terminal count.
    check_counter_within_range: assert property (
        @(posedge C_100Mhz) contador <= LIMIT
    );

    // When not at terminal count, counter increments by 1.
    check_counter_increments_when_not_limit: assert property (
        @(posedge C_100Mhz) ($past(contador) != LIMIT) |-> (contador == $past(contador) + 1)
    );

    // When not at terminal count, output remains stable.
    check_output_stable_when_not_limit: assert property (
        @(posedge C_100Mhz) ($past(contador) != LIMIT) |-> (C_1Hz == $past(C_1Hz))
    );

    // At terminal count, counter clears and output toggles.
    check_rollover_behavior: assert property (
        @(posedge C_100Mhz) ($past(contador) == LIMIT) |-> (contador == 32'd0) && (C_1Hz == ~$past(C_1Hz))
    );

    // Output can change only when previous count was terminal.
    check_toggle_only_on_rollover: assert property (
        @(posedge C_100Mhz) $changed(C_1Hz) |-> ($past(contador) == LIMIT)
    );

    // Any change on output is a true toggle (complement).
    check_toggle_is_complement: assert property (
        @(posedge C_100Mhz) $changed(C_1Hz) |-> (C_1Hz == ~$past(C_1Hz))
    );

    // Any toggle coincides with counter cleared to zero.
    check_toggle_clears_counter: assert property (
        @(posedge C_100Mhz) $changed(C_1Hz) |-> (contador == 32'd0)
    );

    // Next counter value is either previous+1 or zero (rollover).
    check_next_count_inc_or_zero: assert property (
        @(posedge C_100Mhz) (contador == ($past(contador) + 1)) || (contador == 32'd0)
    );

    // If counter becomes zero without having been zero, previous must have been terminal.
    check_zero_arrival_cause: assert property (
        @(posedge C_100Mhz) ((contador == 32'd0) && ($past(contador) != 32'd0)) |-> ($past(contador) == LIMIT)
    );

    // No consecutive-cycle toggles on the output.
    check_no_back_to_back_toggles: assert property (
        @(posedge C_100Mhz) $changed(C_1Hz) |-> ##1 !$changed(C_1Hz)
    );

endmodule