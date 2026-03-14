module mux2to1_sva (
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // On S rising, output selects B.
    select_B_on_S_rise: assert property (
        @(posedge S) Y == B
    );

    // On S falling, output selects A.
    select_A_on_S_fall: assert property (
        @(negedge S) Y == A
    );

    // On A rising, Y matches the mux equation.
    equation_hold_on_A_rise: assert property (
        @(posedge A) Y == ((!S && A) | (S && B))
    );

    // On A falling, Y matches the mux equation.
    equation_hold_on_A_fall: assert property (
        @(negedge A) Y == ((!S && A) | (S && B))
    );

    // On B rising, Y matches the mux equation.
    equation_hold_on_B_rise: assert property (
        @(posedge B) Y == ((!S && A) | (S && B))
    );

    // On B falling, Y matches the mux equation.
    equation_hold_on_B_fall: assert property (
        @(negedge B) Y == ((!S && A) | (S && B))
    );

    // When S=0 and A rises, Y follows A.
    y_follows_A_when_S0_rise: assert property (
        @(posedge A) (!S) |-> (Y == A)
    );

    // When S=0 and A falls, Y follows A.
    y_follows_A_when_S0_fall: assert property (
        @(negedge A) (!S) |-> (Y == A)
    );

    // When S=1 and B rises, Y follows B.
    y_follows_B_when_S1_rise: assert property (
        @(posedge B) (S) |-> (Y == B)
    );

    // When S=1 and B falls, Y follows B.
    y_follows_B_when_S1_fall: assert property (
        @(negedge B) (S) |-> (Y == B)
    );
endmodule