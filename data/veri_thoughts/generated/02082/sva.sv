module sky130_fd_sc_hd__nor3b_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N
);

    // Y implements C_N & ~(A | B).
    check_functional_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        (Y == (C_N & ~(A | B)))
    );

    // If A is HIGH, Y must be LOW.
    check_y_zero_when_A_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        A |-> (Y == 1'b0)
    );

    // If B is HIGH, Y must be LOW.
    check_y_zero_when_B_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        B |-> (Y == 1'b0)
    );

    // If C_N is LOW, Y must be LOW.
    check_y_zero_when_C_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        (!C_N) |-> (Y == 1'b0)
    );

    // If C_N is HIGH and A==0 and B==0, Y must be HIGH.
    check_y_one_when_AB_zero_and_C_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        (C_N && !A && !B) |-> (Y == 1'b1)
    );

    // If Y is HIGH, then C_N==1 and A==0 and B==0.
    check_y_one_implies_inputs_condition: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        Y |-> (C_N && !A && !B)
    );

    // When A==0 and B==0, Y equals C_N.
    check_y_equals_C_when_AB_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        (!A && !B) |-> (Y == C_N)
    );

    // When C_N==1, Y equals NOR of A and B.
    check_y_equals_nor_ab_when_C_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        C_N |-> (Y == ~(A | B))
    );

    // If A or B is HIGH or C_N is LOW, Y must be LOW.
    check_y_zero_when_any_blocking_input: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
        (A || B || !C_N) |-> (Y == 1'b0)
    );

endmodule