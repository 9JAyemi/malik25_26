module ripple_carry_adder_sva #(
    parameter int WIDTH = 4
) (
    input logic clk,
    input logic [WIDTH-1:0] A,
    input logic [WIDTH-1:0] B,
    input logic Cin,
    input logic [WIDTH-1:0] S,
    input logic Cout
);

    genvar i;

    // Full result matches A + B + Cin.
    check_total_matches_addition: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Carry-out matches the top bit of the extended addition.
    check_cout_matches_addition_carry: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin)[WIDTH])
    );

    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_prefix_checks
            // Each low-order sum slice matches low-order addition.
            check_prefix_sum_matches_addition: assert property (
                @(posedge clk) S[i:0] == (A[i:0] + B[i:0] + Cin)
            );
        end
    endgenerate

    // Zero operands with zero carry-in produce zero output.
    check_zero_inputs_produce_zero: assert property (
        @(posedge clk) (A == '0 && B == '0 && Cin == 1'b0) |-> (S == '0 && Cout == 1'b0)
    );

    // Adding zero and no carry-in passes A through unchanged.
    check_a_passthrough_when_b_and_cin_zero: assert property (
        @(posedge clk) (B == '0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero and no carry-in passes B through unchanged.
    check_b_passthrough_when_a_and_cin_zero: assert property (
        @(posedge clk) (A == '0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, B})
    );

    // The least-significant sum bit follows full-adder XOR logic.
    check_lsb_sum_logic: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

endmodule