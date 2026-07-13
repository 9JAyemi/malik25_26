module sky130_fd_sc_ls__a21oi_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);
    // Functional equivalence: Y = ~A1 | (A2 & ~B1).
    check_func_equiv: assert property (
        @(posedge CLK) Y == ((~A1) | (A2 & ~B1))
    );

    // If A1 is 0 then Y must be 1.
    check_y_high_when_a1_low: assert property (
        @(posedge CLK) (~A1) |-> (Y == 1'b1)
    );

    // If A1=1 and A2=0 then Y=0.
    check_y_low_when_a1_1_a2_0: assert property (
        @(posedge CLK) (A1 & ~A2) |-> (Y == 1'b0)
    );

    // If A1=1 and B1=1 then Y=0.
    check_y_low_when_a1_1_b1_1: assert property (
        @(posedge CLK) (A1 & B1) |-> (Y == 1'b0)
    );

    // If A2=1 and B1=0 then Y=1.
    check_y_high_when_a2_1_b1_0: assert property (
        @(posedge CLK) (A2 & ~B1) |-> (Y == 1'b1)
    );

    // When A1=1 and B1=0, Y equals A2.
    check_y_eq_a2_when_a1_1_b1_0: assert property (
        @(posedge CLK) (A1 & ~B1) |-> (Y == A2)
    );

    // When B1=1, Y equals ~A1.
    check_y_eq_not_a1_when_b1_1: assert property (
        @(posedge CLK) (B1) |-> (Y == ~A1)
    );

    // If Y is 0 then A1=1 and (A2=0 or B1=1).
    check_inputs_when_y0: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (A1 & (~A2 | B1))
    );

    // If Y is 1 then (~A1) or (A2=1 and B1=0).
    check_inputs_when_y1: assert property (
        @(posedge CLK) (Y == 1'b1) |-> ((~A1) | (A2 & ~B1))
    );

    // With B1=0, Y equals (~A1 | A2).
    check_simplify_when_b1_0: assert property (
        @(posedge CLK) (~B1) |-> (Y == ((~A1) | A2))
    );
endmodule