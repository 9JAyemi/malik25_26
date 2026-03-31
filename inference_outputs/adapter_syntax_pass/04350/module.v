module matrix_multiplier(
    input clk,
    input reset,
    input [15:0] matrix1,
    input [15:0] matrix2,
    output [15:0] result
);

reg [15:0] temp[3:0];

always @(posedge clk) begin
    if (reset) begin
        temp[0] <= 0;
        temp[1] <= 0;
        temp[2] <= 0;
        temp[3] <= 0;
    end else begin
        temp[0] <= matrix1[3:0] * matrix2[0] + matrix1[7:4] * matrix2[4] + matrix1[11:8] * matrix2[8] + matrix1[15:12] * matrix2[12];
        temp[1] <= matrix1[3:0] * matrix2[1] + matrix1[7:4] * matrix2[5] + matrix1[11:8] * matrix2[9] + matrix1[15:12] * matrix2[13];
        temp[2] <= matrix1[3:0] * matrix2[2] + matrix1[7:4] * matrix2[6] + matrix1[11:8] * matrix2[10] + matrix1[15:12] * matrix2[14];
        temp[3] <= matrix1[3:0] * matrix2[3] + matrix1[7:4] * matrix2[7] + matrix1[11:8] * matrix2[11] + matrix1[15:12] * matrix2[15];
    end
end

assign result = {temp[3], temp[2], temp[1], temp[0]};

endmodule