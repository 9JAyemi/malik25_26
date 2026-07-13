module bitwise_or_sva(
    input logic [7:0] A,
    input logic [7:0] B,
    input logic enable,
    input logic clk,
    input logic [7:0] result
);

    // When enabled, result captures the sampled bitwise OR of A and B.
    check_enabled_or_update: assert property (
        @(posedge clk) enable |=> (result == $past(A | B))
    );

    // If A is zero when enabled, result captures B.
    check_a_zero_passes_b: assert property (
        @(posedge clk) (enable && (A == 8'h00)) |=> (result == $past(B))
    );

    // If B is zero when enabled, result captures A.
    check_b_zero_passes_a: assert property (
        @(posedge clk) (enable && (B == 8'h00)) |=> (result == $past(A))
    );

    // If both inputs are equal when enabled, result captures that value.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (enable && (A == B)) |=> (result == $past(A))
    );

    // If A and B have no overlapping 1 bits when enabled, OR matches XOR.
    check_disjoint_inputs_match_xor: assert property (
        @(posedge clk) (enable && ((A & B) == 8'h00)) |=> (result == ($past(A) ^ $past(B)))
    );

    // If all 1 bits of A are already present in B when enabled, result captures B.
    check_a_subset_of_b: assert property (
        @(posedge clk) (enable && ((A & B) == A)) |=> (result == $past(B))
    );

    // If all 1 bits of B are already present in A when enabled, result captures A.
    check_b_subset_of_a: assert property (
        @(posedge clk) (enable && ((A & B) == B)) |=> (result == $past(A))
    );

    // If either input is all ones when enabled, result becomes all ones.
    check_all_ones_dominates: assert property (
        @(posedge clk) (enable && ((A == 8'hFF) || (B == 8'hFF))) |=> (result == 8'hFF)
    );

endmodule