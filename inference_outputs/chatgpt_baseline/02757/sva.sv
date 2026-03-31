module eight_to_one_sva (
    input logic [2:0] A1,
    input logic [2:0] A2,
    input logic [2:0] B1,
    input logic [2:0] B2,
    input logic [2:0] C1,
    input logic [2:0] C2,
    input logic [2:0] D1,
    input logic [2:0] D2,
    input logic [2:0] Y
);
    // No clock/reset in RTL; purely combinational. Use posedge of A1[0] as sampling event.

    // Y must equal one of the eight inputs.
    check_Y_is_from_inputs: assert property (
        @(posedge A1[0]) (Y == A1) || (Y == A2) || (Y == B1) || (Y == B2) || (Y == C1) || (Y == C2) || (Y == D1) || (Y == D2)
    );

    // No input can be strictly greater than Y (Y is an upper bound).
    check_Y_is_upper_bound: assert property (
        @(posedge A1[0]) (Y >= A1) && (Y >= A2) && (Y >= B1) && (Y >= B2) && (Y >= C1) && (Y >= C2) && (Y >= D1) && (Y >= D2)
    );

    // If A1 is strictly greater than all others, Y equals A1.
    check_strict_max_A1: assert property (
        @(posedge A1[0]) (A1 > A2) && (A1 > B1) && (A1 > B2) && (A1 > C1) && (A1 > C2) && (A1 > D1) && (A1 > D2) |-> (Y == A1)
    );

    // If A2 is strictly greater than all others, Y equals A2.
    check_strict_max_A2: assert property (
        @(posedge A1[0]) (A2 > A1) && (A2 > B1) && (A2 > B2) && (A2 > C1) && (A2 > C2) && (A2 > D1) && (A2 > D2) |-> (Y == A2)
    );

    // If B1 is strictly greater than all others, Y equals B1.
    check_strict_max_B1: assert property (
        @(posedge A1[0]) (B1 > A1) && (B1 > A2) && (B1 > B2) && (B1 > C1) && (B1 > C2) && (B1 > D1) && (B1 > D2) |-> (Y == B1)
    );

    // If B2 is strictly greater than all others, Y equals B2.
    check_strict_max_B2: assert property (
        @(posedge A1[0]) (B2 > A1) && (B2 > A2) && (B2 > B1) && (B2 > C1) && (B2 > C2) && (B2 > D1) && (B2 > D2) |-> (Y == B2)
    );

    // If C1 is strictly greater than all others, Y equals C1.
    check_strict_max_C1: assert property (
        @(posedge A1[0]) (C1 > A1) && (C1 > A2) && (C1 > B1) && (C1 > B2) && (C1 > C2) && (C1 > D1) && (C1 > D2) |-> (Y == C1)
    );

    // If C2 is strictly greater than all others, Y equals C2.
    check_strict_max_C2: assert property (
        @(posedge A1[0]) (C2 > A1) && (C2 > A2) && (C2 > B1) && (C2 > B2) && (C2 > C1) && (C2 > D1) && (C2 > D2) |-> (Y == C2)
    );

    // If D1 is strictly greater than all others, Y equals D1.
    check_strict_max_D1: assert property (
        @(posedge A1[0]) (D1 > A1) && (D1 > A2) && (D1 > B1) && (D1 > B2) && (D1 > C1) && (D1 > C2) && (D1 > D2) |-> (Y == D1)
    );

    // If D2 is strictly greater than all others, Y equals D2.
    check_strict_max_D2: assert property (
        @(posedge A1[0]) (D2 > A1) && (D2 > A2) && (D2 > B1) && (D2 > B2) && (D2 > C1) && (D2 > C2) && (D2 > D1) |-> (Y == D2)
    );
endmodule