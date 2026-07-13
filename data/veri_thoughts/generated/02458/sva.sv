module combinational_logic_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y must equal the RTL combinational equation.
    check_y_equation: assert property (
        @(posedge CLK)
        Y == ((~A1 & B1 & C1) | (~A1 & ~B2 & ~C1) | (A1 & ~B1 & ~C1) | (A2 & ~B1 & ~C1) | (A2 & B2 & C1))
    );

    // If (~A1 & B1 & C1) holds, Y must be 1.
    check_term1_sets_y: assert property (
        @(posedge CLK)
        (~A1 & B1 & C1) |-> (Y == 1'b1)
    );

    // If (~A1 & ~B2 & ~C1) holds, Y must be 1.
    check_term2_sets_y: assert property (
        @(posedge CLK)
        (~A1 & ~B2 & ~C1) |-> (Y == 1'b1)
    );

    // If (A1 & ~B1 & ~C1) holds, Y must be 1.
    check_term3_sets_y: assert property (
        @(posedge CLK)
        (A1 & ~B1 & ~C1) |-> (Y == 1'b1)
    );

    // If (A2 & ~B1 & ~C1) holds, Y must be 1.
    check_term4_sets_y: assert property (
        @(posedge CLK)
        (A2 & ~B1 & ~C1) |-> (Y == 1'b1)
    );

    // If (A2 & B2 & C1) holds, Y must be 1.
    check_term5_sets_y: assert property (
        @(posedge CLK)
        (A2 & B2 & C1) |-> (Y == 1'b1)
    );

    // With C1=1 and B1=0, if A2=0 or B2=0 then no term can assert Y.
    check_y_zero_c1_high_b1_low_blocked: assert property (
        @(posedge CLK)
        (C1 & ~B1 & (~A2 | ~B2)) |-> (Y == 1'b0)
    );

    // With C1=0 and B1=1, if A1=1 or B2=1 then no term can assert Y.
    check_y_zero_c1_low_b1_high_blocked: assert property (
        @(posedge CLK)
        (~C1 & B1 & (A1 | B2)) |-> (Y == 1'b0)
    );

    // With C1=0, B1=0, A1=0, A2=0, B2=1, no term can assert Y.
    check_y_zero_specific_combo1: assert property (
        @(posedge CLK)
        (~C1 & ~B1 & ~A1 & ~A2 & B2) |-> (Y == 1'b0)
    );

    // With C1=1, B1=1, A1=1, and (A2=0 or B2=0), no term can assert Y.
    check_y_zero_specific_combo2: assert property (
        @(posedge CLK)
        (C1 & B1 & A1 & (~A2 | ~B2)) |-> (Y == 1'b0)
    );

endmodule