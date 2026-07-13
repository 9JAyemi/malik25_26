module full_subtractor_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Bin,
    input logic D,
    input logic Bout
);

    // D must equal the full-subtractor difference.
    check_difference_function: assert property (
        @(posedge clk) D == (A ^ B ^ Bin)
    );

    // Bout must equal the full-subtractor borrow equation.
    check_borrow_function: assert property (
        @(posedge clk) Bout == ((~A & B) | (~(A ^ B) & Bin))
    );

    // With Bin low, the block reduces to a half subtractor on A and B.
    check_no_borrow_in_reduction: assert property (
        @(posedge clk) !Bin |-> ((D == (A ^ B)) && (Bout == (~A & B)))
    );

    // With B low, the block subtracts only Bin from A.
    check_b_zero_reduction: assert property (
        @(posedge clk) !B |-> ((D == (A ^ Bin)) && (Bout == (~A & Bin)))
    );

    // When A and B are equal, both outputs must match Bin.
    check_equal_inputs_reduction: assert property (
        @(posedge clk) (A == B) |-> ((D == Bin) && (Bout == Bin))
    );

    // When A is low, borrow is the OR of B and Bin.
    check_a_zero_reduction: assert property (
        @(posedge clk) !A |-> ((D == (B ^ Bin)) && (Bout == (B | Bin)))
    );

    // When A is high, borrow occurs only if both B and Bin are high.
    check_a_one_reduction: assert property (
        @(posedge clk) A |-> ((D == (~(B ^ Bin))) && (Bout == (B & Bin)))
    );

endmodule