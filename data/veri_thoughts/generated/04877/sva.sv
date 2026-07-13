module combinational_logic_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Sampling clock for this combinational DUT.
    
    // X matches the implemented sum-of-products equation.
    check_output_equation: assert property (
        @(posedge clk)
        X == ((~A1 & A2 & B1_N) | (A1 & ~A2 & B1_N) | (A1 & A2 & ~B1_N))
    );

    // With B1_N high, X reduces to A1 XOR A2.
    check_b1n_high_xor_behavior: assert property (
        @(posedge clk)
        B1_N |-> (X == (A1 ^ A2))
    );

    // With B1_N low, X reduces to A1 AND A2.
    check_b1n_low_and_behavior: assert property (
        @(posedge clk)
        ~B1_N |-> (X == (A1 & A2))
    );

    // If X is high, the inputs match one implemented minterm.
    check_x_high_only_on_implemented_minterms: assert property (
        @(posedge clk)
        X |-> ((~A1 & A2 & B1_N) | (A1 & ~A2 & B1_N) | (A1 & A2 & ~B1_N))
    );

    // Any implemented minterm drives X high.
    check_implemented_minterms_drive_high: assert property (
        @(posedge clk)
        ((~A1 & A2 & B1_N) | (A1 & ~A2 & B1_N) | (A1 & A2 & ~B1_N)) |-> X
    );

    // When A1 and A2 are both low, X is low.
    check_both_a_low_forces_x_low: assert property (
        @(posedge clk)
        (~A1 & ~A2) |-> ~X
    );

    // When A1 and A2 are both high, X is the inverse of B1_N.
    check_both_a_high_invert_b1n: assert property (
        @(posedge clk)
        (A1 & A2) |-> (X == ~B1_N)
    );

    // When exactly one of A1 or A2 is high, X follows B1_N.
    check_one_hot_a_inputs_follow_b1n: assert property (
        @(posedge clk)
        (A1 ^ A2) |-> (X == B1_N)
    );

endmodule