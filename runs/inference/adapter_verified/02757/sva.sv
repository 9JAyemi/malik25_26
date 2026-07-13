module eight_to_one_sva (
    input logic clk,
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

// Y must equal the maximum of all eight inputs.
    check_y_is_max_of_all: assert property (
        @(posedge clk)
        Y == max3(max3(max3(A1, A2), max3(B1, B2)), max3(C1, C2), max3(D1, D2))
    );

// A1 must be selected if it is greater than A2 and greater than Y.
    check_a1_selected_when_greater_than_a2_and_y: assert property (
        @(posedge clk)
        (A1 > A2 && A1 > Y) |-> (Y == A1)
    );

// A2 must be selected if it is greater than A1 and greater than Y.
    check_a2_selected_when_greater_than_a1_and_y: assert property (
        @(posedge clk)
        (A2 > A1 && A2 > Y) |-> (Y == A2)
    );

// B1 must be selected if it is greater than B2, greater than A1, and greater than Y.
    check_b1_selected_when_greater_than_b2_and_a1_and_y: assert property (
        @(posedge clk)
        (B1 > B2 && B1 > A1 && B1 > Y) |-> (Y == B1)
    );

// B2 must be selected if it is greater than B1, greater than A2, and greater than Y.
    check_b2_selected_when_greater_than_b1_and_a2_and_y: assert property (
        @(posedge clk)
        (B2 > B1 && B2 > A2 && B2 > Y) |-> (Y == B2)
    );

// C1 must be selected if it is greater than C2, greater than A1, A2, B1, and B2, and greater than Y.
    check_c1_selected_when_greater_than_c2_and_a1_a2_b1_b2_and_y: assert property (
        @(posedge clk)
        (C1 > C2 && C1 > A1 && C1 > A2 && C1 > B1 && C1 > B2 && C1 > Y) |-> (Y == C1)
    );

// C2 must be selected if it is greater than C1, greater than A1, A2, B1, and B2, and greater than Y.
    check_c2_selected_when_greater_than_c1_and_a1_a2_b1_b2_and_y: assert property (
        @(posedge clk)
        (C2 > C1 && C2 > A1 && C2 > A2 && C2 > B1 && C2 > B2 && C2 > Y) |-> (Y == C2)
    );

// D1 must be selected if it is greater than D2, greater than A1, A2, B1, B2, C1, and C2, and greater than Y.
    check_d1_selected_when_greater_than_d2_and_a1_a2_b1_b2_c1_c2_and_y: assert property (
        @(posedge clk)
        (D1 > D2 && D1 > A1 && D1 > A2 && D1 > B1 && D1 > B2 && D1 > C1 && D1 > C2 && D1 > Y) |-> (Y == D1)
    );

// D2 must be selected if it is greater than D1, greater than A1, A2, B1, B2, C1, and C2, and greater than Y.
    check_d2_selected_when_greater_than_d1_and_a1_a2_b1_b2_c1_c2_and_y: assert property (
        @(posedge clk)
        (D2 > D1 && D2 > A1 && D2 > A2 && D2 > B1 && D2 > B2 && D2 > C1 && D2 > C2 && D2 > Y) |-> (Y == D2)
    );

endmodule
