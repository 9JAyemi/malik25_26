module my_4input_nand_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // Y equals NAND of A,B,C,D.
    check_y_is_nand4: assert property (
        @(posedge A or posedge B or posedge C or posedge D) Y == ~(A & B & C & D)
    );

    // If any input is 0, Y must be 1.
    check_any_zero_implies_y1: assert property (
        @(posedge A or posedge B or posedge C or posedge D) ((A == 1'b0) || (B == 1'b0) || (C == 1'b0) || (D == 1'b0)) |-> (Y == 1'b1)
    );

    // If all inputs are 1, Y must be 0.
    check_all_ones_implies_y0: assert property (
        @(posedge A or posedge B or posedge C or posedge D) (A && B && C && D) |-> (Y == 1'b0)
    );

    // If Y is 0, then all inputs must be 1.
    check_y0_implies_all_ones: assert property (
        @(posedge A or posedge B or posedge C or posedge D) (Y == 1'b0) |-> (A && B && C && D)
    );

    // If Y is 1, then at least one input must be 0.
    check_y1_implies_any_zero: assert property (
        @(posedge A or posedge B or posedge C or posedge D) (Y == 1'b1) |-> ((A == 1'b0) || (B == 1'b0) || (C == 1'b0) || (D == 1'b0))
    );

    // De Morgan equivalence: Y equals (!A || !B || !C || !D).
    check_demorgan_form: assert property (
        @(posedge A or posedge B or posedge C or posedge D) Y == (!A || !B || !C || !D)
    );

    // On A rising when others are 1, Y must be 0.
    check_posedge_a_all_ones_y0: assert property (
        @(posedge A) (B && C && D) |-> (Y == 1'b0)
    );

    // On B rising when others are 1, Y must be 0.
    check_posedge_b_all_ones_y0: assert property (
        @(posedge B) (A && C && D) |-> (Y == 1'b0)
    );

    // On C rising when others are 1, Y must be 0.
    check_posedge_c_all_ones_y0: assert property (
        @(posedge C) (A && B && D) |-> (Y == 1'b0)
    );

    // On D rising when others are 1, Y must be 0.
    check_posedge_d_all_ones_y0: assert property (
        @(posedge D) (A && B && C) |-> (Y == 1'b0)
    );
endmodule