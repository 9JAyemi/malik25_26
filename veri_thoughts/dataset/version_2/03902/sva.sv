module full_subtractor_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Bin,
    input logic D,
    input logic Bout
);

    // No RTL reset is present; clk is a sampling clock for combinational checks.

    // Difference is the xor of A, B, and Bin.
    check_difference_equation: assert property (
        @(posedge clk) D == (A ^ B ^ Bin)
    );

    // Borrow matches the implemented two-half-subtractor expression.
    check_borrow_equation: assert property (
        @(posedge clk) Bout == (((~A) & B) | ((~(A ^ B)) & Bin))
    );

    // 0 - 0 - 0 gives zero difference and no borrow.
    check_zero_minus_zero_no_borrowin: assert property (
        @(posedge clk) (!A && !B && !Bin) |-> (D == 1'b0 && Bout == 1'b0)
    );

    // 0 - 0 - 1 gives difference one and borrow one.
    check_zero_minus_zero_with_borrowin: assert property (
        @(posedge clk) (!A && !B && Bin) |-> (D == 1'b1 && Bout == 1'b1)
    );

    // 0 - 1 - 0 gives difference one and borrow one.
    check_zero_minus_one_no_borrowin: assert property (
        @(posedge clk) (!A && B && !Bin) |-> (D == 1'b1 && Bout == 1'b1)
    );

    // 0 - 1 - 1 gives zero difference and borrow one.
    check_zero_minus_one_with_borrowin: assert property (
        @(posedge clk) (!A && B && Bin) |-> (D == 1'b0 && Bout == 1'b1)
    );

    // 1 - 0 - 0 gives difference one and no borrow.
    check_one_minus_zero_no_borrowin: assert property (
        @(posedge clk) (A && !B && !Bin) |-> (D == 1'b1 && Bout == 1'b0)
    );

    // 1 - 0 - 1 gives zero difference and no borrow.
    check_one_minus_zero_with_borrowin: assert property (
        @(posedge clk) (A && !B && Bin) |-> (D == 1'b0 && Bout == 1'b0)
    );

    // 1 - 1 - 0 gives zero difference and no borrow.
    check_one_minus_one_no_borrowin: assert property (
        @(posedge clk) (A && B && !Bin) |-> (D == 1'b0 && Bout == 1'b0)
    );

    // 1 - 1 - 1 gives difference one and borrow one.
    check_one_minus_one_with_borrowin: assert property (
        @(posedge clk) (A && B && Bin) |-> (D == 1'b1 && Bout == 1'b1)
    );

endmodule