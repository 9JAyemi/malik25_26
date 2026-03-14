module dff_with_set_sva (
    input logic CLK,
    input logic D,
    input logic SET,
    input logic Q
);
    // Q on the next cycle equals 1 if SET was 1, else D from the previous cycle.
    q_next_matches_function: assert property (
        @(posedge CLK) 1'b1 |-> ##1 (Q == ($past(SET) ? 1'b1 : $past(D)))
    );

    // SET takes priority: if SET is 1, Q is 1 on the next cycle.
    set_forces_q_high_next: assert property (
        @(posedge CLK) SET |=> (Q == 1'b1)
    );

    // When SET is 0 and D is 1, Q is 1 on the next cycle.
    data1_updates_q_next_when_no_set: assert property (
        @(posedge CLK) (!SET && (D == 1'b1)) |=> (Q == 1'b1)
    );

    // When SET is 0 and D is 0, Q is 0 on the next cycle.
    data0_updates_q_next_when_no_set: assert property (
        @(posedge CLK) (!SET && (D == 1'b0)) |=> (Q == 1'b0)
    );

    // Any change in Q must be caused by prior SET=1 or D differing from prior Q.
    q_change_requires_cause: assert property (
        @(posedge CLK) (Q != $past(Q)) |-> ($past(SET) || ($past(D) != $past(Q)))
    );

    // If previously SET=0 and D matched prior Q, Q must not change now.
    q_stable_when_no_cause: assert property (
        @(posedge CLK) (!$past(SET) && ($past(D) == $past(Q))) |-> (Q == $past(Q))
    );
endmodule