module nor4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // Y must equal (~A & ~B) | (~C & ~D).
    check_function_equivalence: assert property (
        @(posedge clk) Y == ((~(A | B)) | (~(C | D)))
    );

    // If A and B are both 0, Y must be 1.
    check_y_high_when_ab00: assert property (
        @(posedge clk) (A == 1'b0) && (B == 1'b0) |-> (Y == 1'b1)
    );

    // If C and D are both 0, Y must be 1.
    check_y_high_when_cd00: assert property (
        @(posedge clk) (C == 1'b0) && (D == 1'b0) |-> (Y == 1'b1)
    );

    // If each pair has at least one '1', Y must be 0.
    check_y_low_when_each_pair_has_one: assert property (
        @(posedge clk) ((A | B) && (C | D)) |-> (Y == 1'b0)
    );

    // If A and B are both 1, Y equals (~C & ~D).
    check_y_equals_notC_and_notD_when_ab11: assert property (
        @(posedge clk) (A == 1'b1) && (B == 1'b1) |-> (Y == ((~C) & (~D)))
    );

    // If Y is 1, at least one pair (A,B) or (C, D) is 00.
    check_y1_implies_some_pair_zero: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((~A & ~B) || (~C & ~D))
    );

    // Rising A with others stable cannot cause Y to rise.
    monotone_no_y_rise_on_A_rise: assert property (
        @(posedge clk) $rose(A) && $stable(B) && $stable(C) && $stable(D) |-> !$rose(Y)
    );

    // Rising C with others stable cannot cause Y to rise.
    monotone_no_y_rise_on_C_rise: assert property (
        @(posedge clk) $rose(C) && $stable(A) && $stable(B) && $stable(D) |-> !$rose(Y)
    );

    // Falling A with B=0 and others stable forces Y=1.
    force_y1_on_A_fall_with_B0: assert property (
        @(posedge clk) $fell(A) && (B == 1'b0) && $stable(B) && $stable(C) && $stable(D) |-> (Y == 1'b1)
    );

    // Falling C with D=0 and others stable forces Y=1.
    force_y1_on_C_fall_with_D0: assert property (
        @(posedge clk) $fell(C) && (D == 1'b0) && $stable(A) && $stable(B) && $stable(D) |-> (Y == 1'b1)
    );
endmodule