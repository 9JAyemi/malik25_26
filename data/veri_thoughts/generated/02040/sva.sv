module mux_2to1_sva (
    input  logic CLK,  // External sampling clock (RTL is pure combinational)
    input  logic A,
    input  logic B,
    input  logic SEL,
    input  logic Y
);
    // Core mux function: Y equals B when SEL=1, else A.
    check_mux_function: assert property (
        @(posedge CLK) Y == (SEL ? B : A)
    );

    // When SEL is 1, Y must equal B.
    check_sel1_routes_B: assert property (
        @(posedge CLK) SEL |-> (Y == B)
    );

    // When SEL is 0, Y must equal A.
    check_sel0_routes_A: assert property (
        @(posedge CLK) !SEL |-> (Y == A)
    );

    // If A and B are equal, Y must equal that value regardless of SEL.
    check_equal_inputs_passthrough: assert property (
        @(posedge CLK) (A == B) |-> (Y == A)
    );

    // If Y differs from A, then SEL must be 1 and Y must be B.
    check_y_not_a_implies_sel1_b: assert property (
        @(posedge CLK) (Y != A) |-> (SEL && (Y == B))
    );

    // If Y differs from B, then SEL must be 0 and Y must be A.
    check_y_not_b_implies_sel0_a: assert property (
        @(posedge CLK) (Y != B) |-> (!SEL && (Y == A))
    );

    // If Y equals A, then either SEL is 0 or inputs are equal.
    check_y_eq_a_implication: assert property (
        @(posedge CLK) (Y == A) |-> (!SEL || (A == B))
    );

    // If Y equals B, then either SEL is 1 or inputs are equal.
    check_y_eq_b_implication: assert property (
        @(posedge CLK) (Y == B) |-> (SEL || (A == B))
    );
endmodule