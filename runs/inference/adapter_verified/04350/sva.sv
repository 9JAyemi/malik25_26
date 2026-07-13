module matrix_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] matrix1,
    input logic [15:0] matrix2,
    input logic [15:0] result
);

// Reset clears the result on the next cycle.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |=> (result == 16'h0000)
    );

// The upper 16 bits of result are always zero.
    check_result_upper_zero: assert property (
        @(posedge clk) disable iff (reset) result[31:16] == 16'h0000
    );

// The lower 16 bits of result are the sum of the four 16-bit products.
    check_result_lower_sum: assert property (
        @(posedge clk) disable iff (reset)
            result[15:0] == (
                (matrix1[3:0] * matrix2[0]) +
                (matrix1[7:4] * matrix2[4]) +
                (matrix1[11:8] * matrix2[8]) +
                (matrix1[15:12] * matrix2[12])
            )
    );

// A zero matrix2 value produces a zero result.
    check_zero_matrix2_zero_result: assert property (
        @(posedge clk) disable iff (reset)
            (matrix2 == 16'h0000) |-> (result == 16'h0000)
    );

// A zero matrix1 value produces a zero result.
    check_zero_matrix1_zero_result: assert property (
        @(posedge clk) disable iff (reset)
            (matrix1 == 16'h0000) |-> (result == 16'h0000)
    );

// A zero matrix2[0] term clears the result bit 0.
    check_zero_term0_clears_lsb: assert property (
        @(posedge clk) disable iff (reset)
            (matrix2[0] == 16'h0000) |-> (result[0] == 1'b0)
    );

// A zero matrix2[4] term clears the result bit 4.
    check_zero_term4_clears_bit4: assert property (
        @(posedge clk) disable iff (reset)
            (matrix2[4] == 16'h0000) |-> (result[4] == 1'b0)
    );

// A zero matrix2[8] term clears the result bit 8.
    check_zero_term8_clears_bit8: assert property (
        @(posedge clk) disable iff (reset)
            (matrix2[8] == 16'h0000) |-> (result[8] == 1'b0)
    );

// A zero matrix2[12] term clears the result bit 12.
    check_zero_term12_clears_bit12: assert property (
        @(posedge clk) disable iff (reset)
            (matrix2[12] == 16'h0000) |-> (result[12] == 1'b0)
    );

endmodule
