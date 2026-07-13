module karnaugh_map_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic F
);

// F equals A & ~B & ~C when A=1, B=0, C=0.
    check_f_true_m3: assert property (
        @(posedge clk) (A && !B && !C) |-> (F == 1'b1)
    );

// F equals A & ~B & C when A=1, B=0, C=1.
    check_f_true_m2: assert property (
        @(posedge clk) (A && !B && C) |-> (F == 1'b1)
    );

// F equals A & B & ~C when A=1, B=1, C=0.
    check_f_true_m1: assert property (
        @(posedge clk) (A && B && !C) |-> (F == 1'b1)
    );

// F equals A & B & C when A=1, B=1, C=1.
    check_f_true_m0: assert property (
        @(posedge clk) (A && B && C) |-> (F == 1'b1)
    );

// F equals ~A & ~B & C when A=0, B=0, C=1.
    check_f_true_not_a_not_b_c: assert property (
        @(posedge clk) (!A && !B && C) |-> (F == 1'b1)
    );

// F equals ~A & B & C when A=0, B=1, C=1.
    check_f_true_not_a_b_c: assert property (
        @(posedge clk) (!A && B && C) |-> (F == 1'b1)
    );

// F equals ~A & B & ~C when A=0, B=1, C=0.
    check_f_true_not_a_b_not_c: assert property (
        @(posedge clk) (!A && B && !C) |-> (F == 1'b1)
    );

// F equals ~A & ~B & ~C when A=0, B=0, C=0.
    check_f_true_not_a_not_b_not_c: assert property (
        @(posedge clk) (!A && !B && !C) |-> (F == 1'b1)
    );

// F equals 0 when A=0 and B=0 (regardless of C).
    check_f_zero_when_a0_b0: assert property (
        @(posedge clk) (!A && !B) |-> (F == 1'b0)
    );

// F equals 0 when A=0 and B=1 (regardless of C).
    check_f_zero_when_a0_b1: assert property (
        @(posedge clk) (!A && B) |-> (F == 1'b0)
    );

// F equals 0 when A=1 and B=0 (regardless of C).
    check_f_zero_when_a1_b0: assert property (
        @(posedge clk) (A && !B) |-> (F == 1'b0)
    );

endmodule
