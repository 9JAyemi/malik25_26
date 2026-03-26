module adder_8bit_sva(
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] sum,
    input logic carry_out
);

    // Outputs match the 9-bit zero-extended addition of A and B.
    check_result_matches_extended_addition: assert property (
        @(posedge clk) {carry_out, sum} == ({1'b0, A} + {1'b0, B})
    );

    // Zero on A passes B through with no carry.
    check_a_zero_passes_b: assert property (
        @(posedge clk) (A == 8'h00) |-> (sum == B && carry_out == 1'b0)
    );

    // Zero on B passes A through with no carry.
    check_b_zero_passes_a: assert property (
        @(posedge clk) (B == 8'h00) |-> (sum == A && carry_out == 1'b0)
    );

    // 8'hFF plus 8'h01 wraps sum and raises carry.
    check_overflow_boundary_ff_plus_01: assert property (
        @(posedge clk) (A == 8'hFF && B == 8'h01) |-> (sum == 8'h00 && carry_out == 1'b1)
    );

    // 8'hFF plus 8'hFF produces 8'hFE with carry high.
    check_max_operands_overflow: assert property (
        @(posedge clk) (A == 8'hFF && B == 8'hFF) |-> (sum == 8'hFE && carry_out == 1'b1)
    );

    // Stable inputs keep the outputs stable.
    check_stable_inputs_keep_outputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> ($stable(sum) && $stable(carry_out))
    );

endmodule