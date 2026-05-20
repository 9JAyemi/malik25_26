module matrix_multiplier_sva (
    input logic clk,
    input logic matrix1,
    input logic matrix2,
    input logic reset,
    input logic temp
);

property ResetSynceotid; @(posedge clk) (reset) |-> (temp) == (0); endproperty
assert property (ResetSynceotid);

property ValidDataeotid; @(posedge clk) ( !reset ) |-> (temp[0] == matrix1[3:0] * matrix2[0] + matrix1[7:4] * matrix2[4] + matrix1[11:8] * matrix2[8] + matrix1[15:12] * matrix2[12]) && (  temp[1] == matrix1[3:0] * matrix2[1] + matrix1[7:4] * matrix2[5] + matrix1[11:8] * matrix2[9] + matrix1[15:12] * matrix2[13] ) && (  temp[2] == matrix1[3:0] * matrix2[2] + matrix1[7:4] * matrix2[6] + matrix1[11:8] * matrix2[10] + matrix1[15:12] * matrix2[14] ) && (  temp[3] == matrix1[3:0] * matrix2[3] + matrix1[7:4] * matrix2[7] + matrix1[11:8] * matrix2[11] + matrix1[15:12] * matrix2[15] ); endproperty
assert property (ValidDataeotid);

endmodule