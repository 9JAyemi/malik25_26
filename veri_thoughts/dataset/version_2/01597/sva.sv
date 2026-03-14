module shift_reg_sva (
    input logic [3:0] D,
    input logic SHL,
    input logic SHR,
    input logic LOAD,
    input logic [3:0] Q
);

    // On next LOAD edge, Q equals D sampled at this LOAD edge.
    load_captures_d_next: assert property (
        @(posedge LOAD) 1'b1 |=> (Q == $past(D))
    );

    // At each LOAD edge after the first, Q equals D from the previous LOAD edge.
    q_matches_prev_d_at_load: assert property (
        @(posedge LOAD) $past($rose(LOAD)) |-> (Q == $past(D))
    );

    // SHL has no effect when LOAD rises; next Q reflects D.
    shl_ignored_on_load: assert property (
        @(posedge LOAD) SHL |=> (Q == $past(D))
    );

    // SHR has no effect when LOAD rises; next Q reflects D.
    shr_ignored_on_load: assert property (
        @(posedge LOAD) SHR |=> (Q == $past(D))
    );

    // SHL and SHR both high are ignored on LOAD; next Q reflects D.
    both_shifts_ignored_on_load: assert property (
        @(posedge LOAD) (SHL && SHR) |=> (Q == $past(D))
    );

    // If D is unchanged across two LOAD pulses, Q is unchanged across them.
    q_stable_when_d_stable_across_loads: assert property (
        @(posedge LOAD) (D == $past(D)) |=> (Q == $past(Q))
    );

    // If D changes between consecutive LOAD pulses, Q changes accordingly.
    q_changes_when_d_changes_across_loads: assert property (
        @(posedge LOAD) (D != $past(D)) |=> (Q != $past(Q))
    );

    // With no shifting requested (SHL=0, SHR=0), next Q still equals D on LOAD.
    no_shift_still_loads_d: assert property (
        @(posedge LOAD) (!SHL && !SHR) |=> (Q == $past(D))
    );

endmodule