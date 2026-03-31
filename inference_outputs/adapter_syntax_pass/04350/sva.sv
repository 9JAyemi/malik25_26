module matrix_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] matrix1,
    input logic [15:0] matrix2,
    input logic [15:0] result
);

    // Reset clears the stored partial products.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |=> (result == 16'h0000)
    );

    // The upper 16 bits of result are always zero.
    check_result_upper_zero: assert property (
        @(posedge clk) disable iff (reset) result[15:8] == 8'h00
    );

    // The lower 8 bits of result match the first partial product.
    check_result_low_byte_matches_first_product: assert property (
        @(posedge clk) disable iff (reset)
        result[7:0] == (matrix1[3:0] * matrix2[0] +
                        matrix1[7:4] * matrix2[4] +
                        matrix1[11:8] * matrix2[8] +
                        matrix1[15:12] * matrix2[12])
    );

    // The next 8 bits of result match the second partial product.
    check_result_mid_byte_matches_second_product: assert property (
        @(posedge clk) disable iff (reset)
        result[15:8] == (matrix1[3:0] * matrix2[1] +
                         matrix1[7:4] * matrix2[5] +
                         matrix1[11:8] * matrix2[9] +
                         matrix1[15:12] * matrix2[13])
    );

endmodule