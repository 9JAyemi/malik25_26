module DFF_with_CLR_E_sva (
    input logic D,
    input logic C,
    input logic E,
    input logic CLR,
    input logic Q
);

    // A sampled high clear forces Q low by the next clock sample.
    check_clear_forces_low: assert property (
        @(posedge C) CLR |=> (Q == 1'b0)
    );

    // With E low, loading D=0 drives Q low on the next clock sample.
    check_enabled_zero_load: assert property (
        @(posedge C) disable iff (CLR) (!E && !D) |=> (Q == 1'b0)
    );

    // A low Q stays low unless E is low and D is high.
    check_low_q_stays_low_without_enabled_one: assert property (
        @(posedge C) disable iff (CLR) ((Q == 1'b0) && (E || !D)) |=> (Q == 1'b0)
    );

    // Any observed rise of Q must come from a prior enabled load of D=1.
    check_rise_requires_enabled_one: assert property (
        @(posedge C) disable iff (CLR || $initstate) $rose(Q) |-> $past(!CLR && !E && D)
    );

endmodule