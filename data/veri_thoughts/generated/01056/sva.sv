module sky130_fd_sc_ms__or2b_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B_N
);
    // X equals A OR NOT B_N.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A | ~B_N)
    );

    // If A is 1, X must be 1.
    check_a_high_forces_x_high: assert property (
        @(posedge clk) A |-> X
    );

    // If B_N is 0, X must be 1.
    check_bn_low_forces_x_high: assert property (
        @(posedge clk) (~B_N) |-> X
    );

    // If A is 0 and B_N is 1, X must be 0.
    check_a0_bn1_forces_x0: assert property (
        @(posedge clk) (!A && B_N) |-> (!X)
    );

    // X is 0 only when A is 0 and B_N is 1.
    check_x0_only_when_a0_bn1: assert property (
        @(posedge clk) (!X) |-> (!A && B_N)
    );

    // Truth-table corner: A=0, B_N=0 => X=1.
    check_tt_a0_bn0_x1: assert property (
        @(posedge clk) (!A && !B_N) |-> X
    );

    // Truth-table corner: A=1, B_N=0 => X=1.
    check_tt_a1_bn0_x1: assert property (
        @(posedge clk) (A && !B_N) |-> X
    );

    // Truth-table corner: A=1, B_N=1 => X=1.
    check_tt_a1_bn1_x1: assert property (
        @(posedge clk) (A && B_N) |-> X
    );

    // Truth-table corner: A=0, B_N=1 => X=0.
    check_tt_a0_bn1_x0: assert property (
        @(posedge clk) (!A && B_N) |-> (!X)
    );
endmodule