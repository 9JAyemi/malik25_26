module matrix_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] matrix1,
    input logic [15:0] matrix2,
    output logic [15:0] result
);

    // Reset behavior: At reset, result should be 0
    reset_behavior: assert property (
        @(posedge clk) disable iff (!reset) (result == 16'b0)
    );

    // Sequential logic: temp registers should be initialized to 0 on reset
    temp_reset: assert property (
        @(posedge clk) disable iff (!reset) (temp[0] == 16'b0 && temp[1] == 16'b0 && temp[2] == 16'b0 && temp[3] == 16'b0)
    );

    // Sequential logic: temp registers should be updated correctly on the rising edge of clk
    temp_update: assert property (
        @(posedge clk) disable iff (!reset) (
            temp[0] == matrix1[3:0] * matrix2[0] + matrix1[7:4] * matrix2[4] + matrix1[11:8] * matrix2[8] + matrix1[15:12] * matrix2[12] &&
            temp[1] == matrix1[3:0] * matrix2[1] + matrix1[7:4] * matrix2[5] + matrix1[11:8] * matrix2[9] + matrix1[15:12] * matrix2[13] &&
            temp[2] == matrix1[3:0] * matrix2[2] + matrix1[7:4] * matrix2[6] + matrix1[11:8] * matrix2[10] + matrix1[15:12] * matrix2[14] &&
            temp[3] == matrix1[3:0] * matrix2[3] + matrix1[7:4] * matrix2[7] + matrix1[11:8] * matrix2[11] + matrix1[15:12] * matrix2[15]
        )
    );

    // Combinational logic: result should be the concatenation of temp registers
    result_assignment: assert property (
        @(posedge clk) disable iff (!reset) (result == {temp[3], temp[2], temp[1], temp[0]})
    );

endmodule