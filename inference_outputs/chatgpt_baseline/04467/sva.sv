module RegisterAdd__parameterized5_sva
  #(parameter N = 23)
  (
    input logic [N-1:0] Q,
    input logic [0:0]   E,
    input logic [N-1:0] D,
    input logic         CLK,
    input logic [0:0]   AR
  );

    // Active-low reset clears Q to zero.
    check_reset_clears_q: assert property (
        @(posedge CLK) !AR[0] |-> (Q == {N{1'b0}})
    );

    // When enabled, Q accumulates D.
    check_accumulate_on_enable: assert property (
        @(posedge CLK) disable iff (!AR[0])
        E[0] |=> (Q == ($past(Q) + $past(D)))
    );

    // When not enabled, Q holds its value.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (!AR[0])
        !E[0] |=> (Q == $past(Q))
    );

    // Any post-reset change in Q must come from a prior enabled cycle.
    check_q_change_requires_prior_enable: assert property (
        @(posedge CLK) disable iff (!AR[0])
        ($past(AR[0]) && (Q != $past(Q))) |-> $past(E[0])
    );

    // On reset release, the update starts from zero.
    check_reset_release_behavior: assert property (
        @(posedge CLK) disable iff (!AR[0])
        $rose(AR[0]) |=> (Q == ($past(E[0]) ? $past(D) : {N{1'b0}}))
    );

endmodule