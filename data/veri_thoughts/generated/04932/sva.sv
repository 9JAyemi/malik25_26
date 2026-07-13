module two_bit_comparator_sva(
    input logic       clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic       Y
);

    // Y implements the 2-bit unsigned A >= B comparison.
    check_unsigned_compare: assert property (
        @(posedge clk) (Y == (A >= B))
    );

    // When MSBs are equal, Y follows the LSB comparison.
    check_equal_msb_branch: assert property (
        @(posedge clk) (A[1] == B[1]) |-> (Y == (A[0] >= B[0]))
    );

    // If A's MSB is greater than B's MSB, Y must be high.
    check_msb_greater_sets_y: assert property (
        @(posedge clk) (A[1] > B[1]) |-> (Y == 1'b1)
    );

    // If A's MSB is less than B's MSB, Y must be low.
    check_msb_less_clears_y: assert property (
        @(posedge clk) (A[1] < B[1]) |-> (Y == 1'b0)
    );

    // Equal inputs must produce a high output.
    check_equal_inputs_set_y: assert property (
        @(posedge clk) (A == B) |-> (Y == 1'b1)
    );

    // With equal MSBs and smaller LSB, Y must be low.
    check_equal_msb_lsb_less: assert property (
        @(posedge clk) ((A[1] == B[1]) && (A[0] < B[0])) |-> (Y == 1'b0)
    );

    // With equal MSBs and greater-or-equal LSB, Y must be high.
    check_equal_msb_lsb_ge: assert property (
        @(posedge clk) ((A[1] == B[1]) && (A[0] >= B[0])) |-> (Y == 1'b1)
    );

endmodule