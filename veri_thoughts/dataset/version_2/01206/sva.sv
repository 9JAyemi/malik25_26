module my_nor4_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // Y equals (A|B)&(C|D).
    check_y_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
            Y == ((A | B) & (C | D))
    );

    // If A and B are both 0, Y must be 0.
    check_y_zero_if_AB_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
            (!A && !B) |-> (Y == 1'b0)
    );

    // If C and D are both 0, Y must be 0.
    check_y_zero_if_CD_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
            (!C && !D) |-> (Y == 1'b0)
    );

    // Y high implies at least one of A/B and one of C/D are high.
    check_y_high_implies_inputs: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
            (Y == 1'b1) |-> (((A | B) == 1'b1) && ((C | D) == 1'b1))
    );

    // When both OR groups are high, Y must be high.
    check_y_high_when_both_groups_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
            (((A | B) == 1'b1) && ((C | D) == 1'b1)) |-> (Y == 1'b1)
    );

    // When either OR group is low, Y must be low.
    check_y_low_when_any_group_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
            ((((A | B) == 1'b0) || ((C | D) == 1'b0))) |-> (Y == 1'b0)
    );
endmodule