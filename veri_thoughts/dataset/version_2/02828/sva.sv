module nor4_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // Y equals D | ((A|B) & ~C).
    check_functional_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        Y == (D | ((A | B) & ~C))
    );

    // If D is HIGH then Y must be HIGH.
    check_D_dominates: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        D |-> (Y == 1'b1)
    );

    // If C is HIGH and D is LOW then Y must be LOW.
    check_C_high_D_low_forces_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        (C && !D) |-> (Y == 1'b0)
    );

    // If C and D are LOW, Y reduces to A|B.
    check_reduction_when_C0_D0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        (!C && !D) |-> (Y == (A | B))
    );

    // If A,B,D are LOW then Y must be LOW (independent of C).
    check_ABD_low_implies_Y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        (!A && !B && !D) |-> (Y == 1'b0)
    );

    // If C and D are LOW and (A|B) is HIGH then Y must be HIGH.
    check_AB_pass_when_C0_D0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        (!C && !D && (A | B)) |-> (Y == 1'b1)
    );
endmodule