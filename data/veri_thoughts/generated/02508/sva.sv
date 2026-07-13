module majority_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Combinational RTL with no clock/reset; assertions sample on any input edge.

    // Y equals the 3-of-4 majority of A,B,C,D.
    check_y_equiv_majority3: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        (Y == ((A & B & C) | (A & B & D) | (A & C & D) | (B & C & D)))
    );

    // Y is 0 when all inputs are 0.
    check_y_zero_when_all_zero: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((!A && !B && !C && !D) |-> (Y == 1'b0))
    );

    // Y is 0 when exactly A and B are 1.
    check_y_zero_when_AB_only: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((A && B && !C && !D) |-> (Y == 1'b0))
    );

    // Y is 0 when exactly A and C are 1.
    check_y_zero_when_AC_only: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((A && C && !B && !D) |-> (Y == 1'b0))
    );

    // Y is 0 when exactly A and D are 1.
    check_y_zero_when_AD_only: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((A && D && !B && !C) |-> (Y == 1'b0))
    );

    // Y is 0 when exactly B and C are 1.
    check_y_zero_when_BC_only: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((B && C && !A && !D) |-> (Y == 1'b0))
    );

    // Y is 0 when exactly B and D are 1.
    check_y_zero_when_BD_only: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((B && D && !A && !C) |-> (Y == 1'b0))
    );

    // Y is 0 when exactly C and D are 1.
    check_y_zero_when_CD_only: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((C && D && !A && !B) |-> (Y == 1'b0))
    );

    // Y is 1 when A, B, and C are 1.
    check_y_one_when_ABC: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((A && B && C) |-> (Y == 1'b1))
    );

    // Y is 1 when A, B, and D are 1.
    check_y_one_when_ABD: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((A && B && D) |-> (Y == 1'b1))
    );

    // Y is 1 when A, C, and D are 1.
    check_y_one_when_ACD: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((A && C && D) |-> (Y == 1'b1))
    );

    // Y is 1 when B, C, and D are 1.
    check_y_one_when_BCD: assert property (
        @(posedge A or posedge B or posedge C or posedge D or negedge A or negedge B or negedge C or negedge D)
        disable iff (1'b0)
        ((B && C && D) |-> (Y == 1'b1))
    );

endmodule