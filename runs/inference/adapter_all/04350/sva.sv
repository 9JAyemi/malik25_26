module matrix_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] matrix1,
    input logic [15:0] matrix2,
    input logic [15:0] result
);

    // Reset clears the registered result on the next clock.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |=> (result == 16'h0000)
    );

    // The upper nibble of result is always zero after reset.
    check_result_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) result[15:12] == 4'h0
    );

    // The lower three nibbles of result are the previous cycle's computed partial products.
    check_result_lower_nibbles_partial_products: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate |-> (
            result[11:8] == $past(
                matrix1[3:0] * matrix2[0] +
                matrix1[7:4] * matrix2[4] +
                matrix1[11:8] * matrix2[8] +
                matrix1[15:12] * matrix2[12]
            ) &&
            result[7:4] == $past(
                matrix1[3:0] * matrix2[1] +
                matrix1[7:4] * matrix2[5] +
                matrix1[11:8] * matrix2[9] +
                matrix1[15:12] * matrix2[13]
            ) &&
            result[3:0] == $past(
                matrix1[3:0] * matrix2[2] +
                matrix1[7:4] * matrix2[6] +
                matrix1[11:8] * matrix2[10] +
                matrix1[15:12] * matrix2[14]
            )
        )
    );

    // The full result is the previous cycle's computed partial products.
    check_result_full_partial_products: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate |-> (
            result == $past(
                {12'h000,
                 (matrix1[3:0] * matrix2[0] +
                  matrix1[7:4] * matrix2[4] +
                  matrix1[11:8] * matrix2[8] +
                  matrix1[15:12] * matrix2[12])} +
                {12'h000,
                 (matrix1[3:0] * matrix2[1] +
                  matrix1[7:4] * matrix2[5] +
                  matrix1[11:8] * matrix2[9] +
                  matrix1[15:12] * matrix2[13])} +
                {12'h000,
                 (matrix1[3:0] * matrix2[2] +
                  matrix1[7:4] * matrix2[6] +
                  matrix1[11:8] * matrix2[10] +
                  matrix1[15:12] * matrix2[14])}
            )
        )
    );

endmodule