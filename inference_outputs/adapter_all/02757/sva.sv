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
    // Y equals the maximum of all 8 inputs.
    check_y_is_max_of_all: assert property (
        @(posedge A1[0]) Y == (
            ((A1 > A2) ? A1 : A2) >=
            ((B1 > B2) ? B1 : B2) >=
            ((C1 > C2) ? C1 : C2) >=
            ((D1 > D2) ? D1 : D2)
        )
    );

    // If A1 is greater than A2, Y must equal A1.
    check_y_equals_a1_when_a1_gt_a2: assert property (
        @(posedge A1[0]) (A1 > A2) |-> (Y == A1)
    );

    // If A1 is not greater than A2, Y must equal A2.
    check_y_equals_a2_when_a1_le_a2: assert property (
        @(posedge A1[0]) !(A1 > A2) |-> (Y == A2)
    );

    // If B1 is greater than B2 and greater than current Y, Y must equal B1.
    check_y_equals_b1_when_b1_gt_b2_and_gt_y: assert property (
        @(posedge B1[0]) ((B1 > B2) && (B1 > Y)) |-> (Y == B1)
    );

    // If B2 is greater than current Y, Y must equal B2.
    check_y_equals_b2_when_b2_gt_y: assert property (
        @(posedge B1[0]) (B2 > Y) |-> (Y == B2)
    );

    // If C1 is greater than C2 and greater than current Y, Y must equal C1.
    check_y_equals_c1_when_c1_gt_c2_and_gt_y: assert property (
        @(posedge C1[0]) ((C1 > C2) && (C1 > Y)) |-> (Y == C1)
    );

    // If C2 is greater than current Y, Y must equal C2.
    check_y_equals_c2_when_c2_gt_y: assert property (
        @(posedge C1[0]) (C2 > Y) |-> (Y == C2)
    );

    // If D1 is greater than D2 and greater than current Y, Y must equal D1.
    check_y_equals_d1_when_d1_gt_d2_and_gt_y: assert property (
        @(posedge D1[0]) ((D1 > D2) && (D1 > Y)) |-> (Y == D1)
    );

    // If D2 is greater than current Y, Y must equal D2.
    check_y_equals_d2_when_d2_gt_y: assert property (
        @(posedge D1[0]) (D2 > Y) |-> (Y == D2)
    );

    // If A1 is greater than A2 and B1/B2/C1/C2/D1/D2 are all <= A1, Y equals A1.
    check_y_equals_a1_when_a1_max_and_others_le: assert property (
        @(posedge A1[0]) ((A1 > A2) && (A1 >= B1) && (A1 >= B2) && (A1 >= C1) && (A1 >= C2) && (A1 >= D1) && (A1 >= D2)) |-> (Y == A1)
    );

    // If A2 is greater than A1 and B1/B2/C1/C2/D1/D2 are all <= A2, Y equals A2.
    check_y_equals_a2_when_a2_max_and_others_le: assert property (
        @(posedge A1[0]) ((!(A1 > A2)) && (A2 >= B1) && (A2 >= B2) && (A2 >= C1) && (A2 >= C2) && (A2 >= D1) && (A2 >= D2)) |-> (Y == A2)
    );
endmodule