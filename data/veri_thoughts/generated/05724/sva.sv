module sum_diff_sva (
    input logic       clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] S,
    input logic [7:0] D
);

    // S must equal the 8-bit sum of A and B.
    check_sum_function: assert property (
        @(posedge clk) S == (A + B)
    );

    // D must equal the 8-bit difference of A and B.
    check_diff_function: assert property (
        @(posedge clk) D == (A - B)
    );

    // Equal inputs must produce a zero difference.
    check_equal_inputs_zero_diff: assert property (
        @(posedge clk) (A == B) |-> (D == 8'h00)
    );

    // B equal to zero must pass A through both outputs.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 8'h00) |-> ((S == A) && (D == A))
    );

    // A equal to zero must make S equal B and D equal 0 minus B.
    check_zero_a_behavior: assert property (
        @(posedge clk) (A == 8'h00) |-> ((S == B) && (D == (8'h00 - B)))
    );

    // Stable inputs must keep both outputs stable.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> ($stable(S) && $stable(D))
    );

endmodule