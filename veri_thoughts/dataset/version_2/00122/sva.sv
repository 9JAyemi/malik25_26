module Mult4x4_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [7:0]  Result
);

    // Result matches the RTL sum of the two partial products.
    check_result_equation: assert property (
        @(posedge clk) Result == (((A * B[3:2]) << 2) + (A * B[1:0]))
    );

    // Result is the zero-extended low 6 bits of the full 4x4 product.
    check_result_product_mod64: assert property (
        @(posedge clk) Result == ((A * B) & 8'h3F)
    );

    // The upper two bits of Result are always zero after the 6-bit arithmetic.
    check_result_upper_bits_zero: assert property (
        @(posedge clk) Result[7:6] == 2'b00
    );

    // A zero multiplicand forces a zero result.
    check_zero_a: assert property (
        @(posedge clk) (A == 4'h0) |-> (Result == 8'h00)
    );

    // A zero multiplier forces a zero result.
    check_zero_b: assert property (
        @(posedge clk) (B == 4'h0) |-> (Result == 8'h00)
    );

    // When the upper two bits of B are zero, the result matches the full product.
    check_low_range_full_product: assert property (
        @(posedge clk) (B[3:2] == 2'b00) |-> (Result == (A * B))
    );

    // When the lower two bits of B are zero, only the shifted upper partial product contributes.
    check_upper_path_only: assert property (
        @(posedge clk) (B[1:0] == 2'b00) |-> (Result == ((A * B[3:2]) << 2))
    );

    // A zero lower slice in B leaves the two least-significant result bits clear.
    check_upper_path_lsb_zero: assert property (
        @(posedge clk) (B[1:0] == 2'b00) |-> (Result[1:0] == 2'b00)
    );

    // Multiplication by 4 is represented exactly by the aligned upper partial product.
    check_b_four: assert property (
        @(posedge clk) (B == 4'h4) |-> (Result == (A * 4'd4))
    );

    // Stable inputs keep the combinational result stable across sampled cycles.
    check_stable_inputs_stable_result: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(Result)
    );

endmodule