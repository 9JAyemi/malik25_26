module inv_lsb_sva (
    input logic [1:0] data,
    input logic q
);

    // q always equals the inverted least significant input bit.
    check_q_matches_inverted_lsb: assert property (
        @($global_clock) q === ~data[0]
    );

    // q is high when the least significant input bit is low.
    check_q_high_when_lsb_low: assert property (
        @($global_clock) (data[0] === 1'b0) |-> (q === 1'b1)
    );

    // q is low when the least significant input bit is high.
    check_q_low_when_lsb_high: assert property (
        @($global_clock) (data[0] === 1'b1) |-> (q === 1'b0)
    );

    // A rising least significant input bit makes q fall.
    check_q_falls_when_lsb_rises: assert property (
        @($global_clock) $rose(data[0]) |-> $fell(q)
    );

    // A falling least significant input bit makes q rise.
    check_q_rises_when_lsb_falls: assert property (
        @($global_clock) $fell(data[0]) |-> $rose(q)
    );

    // q only changes when the least significant input bit changes.
    check_q_changes_only_with_lsb: assert property (
        @($global_clock) $changed(q) |-> $changed(data[0])
    );

    // Changing only the most significant input bit does not affect q.
    check_msb_has_no_effect_on_q: assert property (
        @($global_clock) ($changed(data[1]) && $stable(data[0])) |-> $stable(q)
    );

endmodule