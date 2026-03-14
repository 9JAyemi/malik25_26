module nor4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Y equals (A|B)&(C|D).
    check_functional_equivalence: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        (Y == (((A || B)) && ((C || D))))
    );

    // Y can be 1 only if at least one of A/B and one of C/D are 1.
    check_y_requires_one_from_each_pair: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        (Y) |-> ((A || B) && (C || D))
    );

    // If both A and B are 0, Y must be 0.
    check_y_zero_when_ab_zero: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        ((!A) && (!B)) |-> (Y == 1'b0)
    );

    // If both C and D are 0, Y must be 0.
    check_y_zero_when_cd_zero: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        ((!C) && (!D)) |-> (Y == 1'b0)
    );

    // If A and C are 1, Y must be 1.
    check_y_when_a_and_c: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        (A && C) |-> (Y == 1'b1)
    );

    // If A and D are 1, Y must be 1.
    check_y_when_a_and_d: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        (A && D) |-> (Y == 1'b1)
    );

    // If B and C are 1, Y must be 1.
    check_y_when_b_and_c: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        (B && C) |-> (Y == 1'b1)
    );

    // If B and D are 1, Y must be 1.
    check_y_when_b_and_d: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        (B && D) |-> (Y == 1'b1)
    );

    // If Y is 1 and A is 0, then B must be 1.
    check_y_and_not_a_implies_b: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        (Y && !A) |-> B
    );

    // If Y is 1 and C is 0, then D must be 1.
    check_y_and_not_c_implies_d: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        (Y && !C) |-> D
    );
endmodule