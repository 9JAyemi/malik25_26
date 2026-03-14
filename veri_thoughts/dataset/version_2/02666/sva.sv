module decoder_2to4_sva (
    input logic A,
    input logic B,
    input logic Y0,
    input logic Y1,
    input logic Y2,
    input logic Y3
);
    // Y0 equals ~(A | B)
    check_y0_is_nor_ab: assert property (
        @(posedge A or negedge A or posedge B or negedge B) Y0 == ~(A | B)
    );

    // Y1 equals ~(A & B)
    check_y1_is_nand_ab: assert property (
        @(posedge A or negedge A or posedge B or negedge B) Y1 == ~(A & B)
    );

    // Y2 equals ~((~A) & B)
    check_y2_is_nor_notA_B: assert property (
        @(posedge A or negedge A or posedge B or negedge B) Y2 == ~((~A) & B)
    );

    // Y3 equals ~(~A | ~B)
    check_y3_is_nand_notA_notB: assert property (
        @(posedge A or negedge A or posedge B or negedge B) Y3 == ~(~A | ~B)
    );

    // Y1 is the logical complement of Y3
    check_y1_complements_y3: assert property (
        @(posedge A or negedge A or posedge B or negedge B) Y1 == ~Y3
    );

    // Truth table: A=0, B=0 -> Y0=1, Y1=1, Y2=1, Y3=0
    check_tt_00: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (!A && !B) |=> (Y0 && Y1 && Y2 && !Y3)
    );

    // Truth table: A=0, B=1 -> Y0=0, Y1=1, Y2=0, Y3=0
    check_tt_01: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (!A && B) |=> (!Y0 && Y1 && !Y2 && !Y3)
    );

    // Truth table: A=1, B=0 -> Y0=0, Y1=1, Y2=1, Y3=0
    check_tt_10: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A && !B) |=> (!Y0 && Y1 && Y2 && !Y3)
    );

    // Truth table: A=1, B=1 -> Y0=0, Y1=0, Y2=1, Y3=1
    check_tt_11: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A && B) |=> (!Y0 && !Y1 && Y2 && Y3)
    );

    // If Y0 is 1, then Y1 must be 1
    check_y0_implies_y1: assert property (
        @(posedge A or negedge A or posedge B or negedge B) Y0 |=> Y1
    );
endmodule