module Test_sva (
    input logic [3:0] cnt,
    input logic [6:0] decr,
    input logic [3:0] next
);

    // Combinational DUT with no explicit clock or reset; sample on $global_clock.

    // next must always equal cnt XOR decr[3:0].
    check_next_matches_xor: assert property (
        @($global_clock) next == (cnt ^ decr[3:0])
    );

    // A zero low nibble in decr passes cnt through unchanged.
    check_zero_low_nibble_passthrough: assert property (
        @($global_clock) (decr[3:0] == 4'h0) |-> (next == cnt)
    );

    // Matching cnt and decr[3:0] must produce zero.
    check_equal_operands_zero_out: assert property (
        @($global_clock) (cnt == decr[3:0]) |-> (next == 4'h0)
    );

    // A low nibble of all ones in decr must invert cnt.
    check_all_ones_low_nibble_inverts_cnt: assert property (
        @($global_clock) (decr[3:0] == 4'hF) |-> (next == ~cnt)
    );

    // If cnt and decr[3:0] do not change, next must not change.
    check_stable_relevant_inputs_hold_output: assert property (
        @($global_clock)
        (!$initstate && (cnt == $past(cnt)) && (decr[3:0] == $past(decr[3:0])))
        |-> (next == $past(next))
    );

    // Changes only in decr[6:4] must not affect next.
    check_upper_bits_ignored: assert property (
        @($global_clock)
        (!$initstate && (cnt == $past(cnt)) && (decr[3:0] == $past(decr[3:0])) &&
         (decr[6:4] != $past(decr[6:4])))
        |-> (next == $past(next))
    );

    // Any change on next must come from cnt or decr[3:0].
    check_output_change_requires_relevant_input_change: assert property (
        @($global_clock)
        (!$initstate && (next != $past(next)))
        |-> ((cnt != $past(cnt)) || (decr[3:0] != $past(decr[3:0])))
    );

endmodule