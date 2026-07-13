module dff_en_sva (
    input logic D,
    input logic C,
    input logic E,
    input logic Q
);

    // Q matches the previous cycle's enabled D value.
    check_q_matches_previous_enabled_d: assert property (
        @(posedge C) disable iff ($initstate)
        Q == $past(E ? D : Q)
    );

    // When enabled, Q captures D on the next clock.
    check_q_captures_d_when_enabled: assert property (
        @(posedge C) disable iff ($initstate)
        E |=> (Q == $past(D))
    );

    // When disabled, Q holds its previous value.
    check_q_holds_when_disabled: assert property (
        @(posedge C) disable iff ($initstate)
        !E |=> (Q == $past(Q))
    );

endmodule