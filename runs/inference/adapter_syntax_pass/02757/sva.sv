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

    // Y must match the RTL's nested max-selection logic.
    check_y_matches_rtl_logic: assert property (
        @($global_clock)
        Y == (
            ((A1 > A2) ? A1 : A2) >=
            ((B1 > B2 && B1 > ((A1 > A2) ? A1 : A2)) ? B1 :
             (B2 > ((A1 > A2) ? A1 : A2)) ? B2 :
             ((C1 > C2 && C1 > ((A1 > A2) ? A1 : A2)) ? C1 :
              (C2 > ((A1 > A2) ? A1 : A2)) ? C2 :
              ((D1 > D2 && D1 > ((A1 > A2) ? A1 : A2)) ? D1 :
               (D2 > ((A1 > A2) ? A1 : A2)) ? D2 :
               ((A1 > A2) ? A1 : A2)))))
    );

    // A1 can drive Y when it is greater than A2.
    check_a1_selects_when_greater_than_a2: assert property (
        @($global_clock)
        (A1 > A2) |-> (Y == A1)
    );

    // A2 can drive Y when it is greater than or equal to A1.
    check_a2_selects_when_not_less_than_a1: assert property (
        @($global_clock)
        (A2 >= A1) |-> (Y == A2)
    );

    // B1 can drive Y when it is greater than B2 and exceeds the current Y.
    check_b1_selects_when_greater_than_b2_and_exceeds_y: assert property (
        @($global_clock)
        ((B1 > B2) && (B1 > Y)) |-> (Y == B1)
    );

    // B2 can drive Y when it is greater than the current Y.
    check_b2_selects_when_exceeds_y: assert property (
        @($global_clock)
        (B2 > Y) |-> (Y == B2)
    );

    // C1 can drive Y when it is greater than C2 and exceeds the current Y.
    check_c1_selects_when_greater_than_c2_and_exceeds_y: assert property (
        @($global_clock)
        ((C1 > C2) && (C1 > Y)) |-> (Y == C1)
    );

    // C2 can drive Y when it is greater than the current Y.
    check_c2_selects_when_exceeds_y: assert property (
        @($global_clock)
        (C2 > Y) |-> (Y == C2)
    );

    // D1 can drive Y when it is greater than D2 and exceeds the current Y.
    check_d1_selects_when_greater_than_d2_and_exceeds_y: assert property (
        @($global_clock)
        ((D1 > D2) && (D1 > Y)) |-> (Y == D1)
    );

    // D2 can drive Y when it is greater than the current Y.
    check_d2_selects_when_exceeds_y: assert property (
        @($global_clock)
        (D2 > Y) |-> (Y == D2)
    );

endmodule