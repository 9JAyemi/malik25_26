module ripple_carry_adder_sva #(parameter int WIDTH = 4) (
    input logic clk,
    input logic [WIDTH-1:0] A,
    input logic [WIDTH-1:0] B,
    input logic CI,
    input logic [WIDTH-1:0] S,
    input logic CO
);

    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_prefix_checks
            // Lower sum bits match addition of the corresponding input slices.
            check_prefix_sum: assert property (
                @(posedge clk) S[i:0] == (A[i:0] + B[i:0] + CI)
            );
        end

        if (WIDTH > 0) begin : gen_lsb_checks
            // The least-significant sum bit matches the full-adder XOR function.
            check_lsb_sum: assert property (
                @(posedge clk) S[0] == (A[0] ^ B[0] ^ CI)
            );
        end

        if (WIDTH == 1) begin : gen_single_bit_checks
            // In the 1-bit case, carry-out matches the full-adder carry function.
            check_single_bit_carry: assert property (
                @(posedge clk) CO == ((A[0] & B[0]) | (CI & (A[0] ^ B[0])))
            );
        end
    endgenerate

    // The concatenated outputs equal the full WIDTH+1-bit sum.
    check_full_sum: assert property (
        @(posedge clk) {CO, S} == ({1'b0, A} + {1'b0, B} + CI)
    );

    // Zero inputs produce zero outputs.
    check_zero_inputs: assert property (
        @(posedge clk) (A == {WIDTH{1'b0}} && B == {WIDTH{1'b0}} && CI == 1'b0) |-> (S == {WIDTH{1'b0}} && CO == 1'b0)
    );

    // Adding zero with no carry-in passes A through unchanged.
    check_pass_a_through: assert property (
        @(posedge clk) (B == {WIDTH{1'b0}} && CI == 1'b0) |-> (S == A && CO == 1'b0)
    );

    // Adding zero with no carry-in passes B through unchanged.
    check_pass_b_through: assert property (
        @(posedge clk) (A == {WIDTH{1'b0}} && CI == 1'b0) |-> (S == B && CO == 1'b0)
    );

    // Carry-in increments an all-ones operand and raises carry-out.
    check_all_ones_plus_carry_in: assert property (
        @(posedge clk) (A == {WIDTH{1'b1}} && B == {WIDTH{1'b0}} && CI == 1'b1) |-> (S == {WIDTH{1'b0}} && CO == 1'b1)
    );

endmodule