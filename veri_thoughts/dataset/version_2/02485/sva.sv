module LFSR25000_sva (
    input logic Clock,
    input logic Reset,      // active-low reset
    input logic Out,
    input logic [14:0] LFSR // internal reg from RTL
);
    localparam logic [14:0] RESET_VAL       = 15'b111111111111111;
    localparam logic [14:0] MATCH_VAL       = 15'b001000010001100;
    localparam logic [14:0] POST_RESET_VAL  = 15'b111111111111110;

    ///// Reset behavior /////
    // While Reset is LOW, Out must be 0.
    check_reset_out_zero: assert property (
        @(posedge Clock) (!Reset) |-> (Out == 1'b0)
    );

    // While Reset is LOW, LFSR must be all ones.
    check_reset_lfsr_ones: assert property (
        @(posedge Clock) (!Reset) |-> (LFSR == RESET_VAL)
    );

    // On Reset rising edge, next LFSR becomes shifted RESET pattern (111...110).
    check_lfsr_on_reset_release: assert property (
        @(posedge Clock) $rose(Reset) |-> (LFSR == POST_RESET_VAL)
    );

    // On Reset rising edge, Out remains 0.
    check_out_on_reset_release: assert property (
        @(posedge Clock) $rose(Reset) |-> (Out == 1'b0)
    );

    ///// Running behavior (Reset HIGH) /////
    // LFSR upper bits shift down by one when running.
    check_lfsr_upper_shift: assert property (
        @(posedge Clock) disable iff (!Reset) $past(Reset) |-> (LFSR[14:1] == $past(LFSR[13:0]))
    );

    // LFSR[0] is feedback XOR of previous LFSR[13] and LFSR[14].
    check_lfsr_feedback_bit: assert property (
        @(posedge Clock) disable iff (!Reset) $past(Reset) |-> (LFSR[0] == ($past(LFSR[13]) ^ $past(LFSR[14])))
    );

    // Out never falls while running (only reset can clear it).
    check_out_never_falls_running: assert property (
        @(posedge Clock) disable iff (!Reset) !$fell(Out)
    );

    // Out can only rise when previous LFSR matched the compare value.
    check_out_rise_only_on_match: assert property (
        @(posedge Clock) disable iff (!Reset) $rose(Out) |-> ($past(LFSR) == MATCH_VAL)
    );

    // If previous LFSR matched, Out must be 1 this cycle.
    check_match_implies_out1: assert property (
        @(posedge Clock) disable iff (!Reset) ($past(LFSR) == MATCH_VAL) |-> (Out == 1'b1)
    );

    // If previous LFSR did not match, Out holds its value.
    check_out_holds_without_match: assert property (
        @(posedge Clock) disable iff (!Reset) ($past(LFSR) != MATCH_VAL) |-> (Out == $past(Out))
    );
endmodule