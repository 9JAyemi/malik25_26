module comparator_sva (
    input logic       clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic       Z
);

    // If A's MSB is greater than B's MSB, Z must be high.
    check_msb_greater_sets_z: assert property (
        @(posedge clk) (A[1] > B[1]) |-> (Z == 1'b1)
    );

    // If A's MSB is less than B's MSB, -1 truncates to 1'b1 on Z.
    check_msb_less_sets_z: assert property (
        @(posedge clk) (A[1] < B[1]) |-> (Z == 1'b1)
    );

    // With equal MSBs, a greater A LSB drives Z high.
    check_lsb_greater_sets_z: assert property (
        @(posedge clk) ((A[1] == B[1]) && (A[0] > B[0])) |-> (Z == 1'b1)
    );

    // With equal MSBs, a lower A LSB also truncates to 1'b1 on Z.
    check_lsb_less_sets_z: assert property (
        @(posedge clk) ((A[1] == B[1]) && (A[0] < B[0])) |-> (Z == 1'b1)
    );

    // Equal inputs drive Z low.
    check_equal_inputs_clear_z: assert property (
        @(posedge clk) (A == B) |-> (Z == 1'b0)
    );

    // Overall implemented behavior is Z high iff A and B differ.
    check_z_matches_input_inequality: assert property (
        @(posedge clk) (Z == (A != B))
    );

endmodule