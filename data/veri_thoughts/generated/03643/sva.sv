module adder_parameterized_sva #(
    parameter int N = 4,
    parameter int M = 4
) (
    input logic clk,
    input logic [N-1:0] A,
    input logic [N-1:0] B,
    input logic Cin,
    input logic [M-1:0] S,
    input logic Cout
);

    localparam int SUM_BITS = (N < M) ? N : M;

    function automatic logic [N:0] full_add_result (
        input logic [N-1:0] a,
        input logic [N-1:0] b,
        input logic cin
    );
        full_add_result = {1'b0, a} + {1'b0, b} + cin;
    endfunction

    generate
        if (SUM_BITS > 0) begin : gen_sum_checks
            for (genvar i = 0; i < SUM_BITS; i++) begin : gen_sum_bit_checks
                // Each visible sum bit matches the corresponding addition result bit.
                check_sum_bit_matches_addition: assert property (
                    @(posedge clk) S[i] == full_add_result(A, B, Cin)[i]
                );
            end
        end
    endgenerate

    // Carry-out matches the addition result carry bit.
    check_cout_matches_addition: assert property (
        @(posedge clk) Cout == full_add_result(A, B, Cin)[N]
    );

    generate
        if (M == N) begin : gen_full_result_check
            // Full output vector matches A + B + Cin when widths align.
            check_full_result_matches_addition: assert property (
                @(posedge clk) {Cout, S} == full_add_result(A, B, Cin)
            );
        end
    endgenerate

    generate
        if (SUM_BITS > 0) begin : gen_add_zero_preserves_a_check
            // Adding zero with no carry preserves the visible bits of A.
            check_add_zero_preserves_a: assert property (
                @(posedge clk) (B == '0 && Cin == 1'b0) |-> (S[SUM_BITS-1:0] == A[SUM_BITS-1:0])
            );
        end
    endgenerate

    // Adding zero with no carry never produces a carry-out.
    check_add_zero_clears_cout: assert property (
        @(posedge clk) (B == '0 && Cin == 1'b0) |-> (Cout == 1'b0)
    );

    generate
        if (SUM_BITS > 0) begin : gen_add_zero_preserves_b_check
            // Adding zero with no carry preserves the visible bits of B.
            check_add_zero_preserves_b: assert property (
                @(posedge clk) (A == '0 && Cin == 1'b0) |-> (S[SUM_BITS-1:0] == B[SUM_BITS-1:0])
            );
        end
    endgenerate

    // Zero operands do not produce a carry-out.
    check_zero_operands_no_carry: assert property (
        @(posedge clk) (A == '0 && B == '0) |-> (Cout == 1'b0)
    );

    generate
        if (SUM_BITS > 0) begin : gen_zero_operands_lsb_check
            // With zero operands, the least-significant visible sum bit follows Cin.
            check_zero_operands_pass_cin_to_lsb: assert property (
                @(posedge clk) (A == '0 && B == '0) |-> (S[0] == Cin)
            );
        end
    endgenerate

endmodule