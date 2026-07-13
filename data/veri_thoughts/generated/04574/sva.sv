module decoder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [15:0] Y
);

    // Y[0] decodes input value 4'b0000.
    check_y0_decode: assert property (
        @(posedge clk) Y[0] == ((~A[3]) & (~A[2]) & (~A[1]) & (~A[0]))
    );

    // Y[1] decodes input value 4'b0001.
    check_y1_decode: assert property (
        @(posedge clk) Y[1] == ((~A[3]) & (~A[2]) & (~A[1]) & A[0])
    );

    // Y[2] decodes input value 4'b0010.
    check_y2_decode: assert property (
        @(posedge clk) Y[2] == ((~A[3]) & (~A[2]) & A[1] & (~A[0]))
    );

    // Y[3] decodes input value 4'b0011.
    check_y3_decode: assert property (
        @(posedge clk) Y[3] == ((~A[3]) & (~A[2]) & A[1] & A[0])
    );

    // Y[4] decodes input value 4'b0100.
    check_y4_decode: assert property (
        @(posedge clk) Y[4] == ((~A[3]) & A[2] & (~A[1]) & (~A[0]))
    );

    // Y[5] decodes input value 4'b0101.
    check_y5_decode: assert property (
        @(posedge clk) Y[5] == ((~A[3]) & A[2] & (~A[1]) & A[0])
    );

    // Y[6] decodes input value 4'b0110.
    check_y6_decode: assert property (
        @(posedge clk) Y[6] == ((~A[3]) & A[2] & A[1] & (~A[0]))
    );

    // Y[7] decodes input value 4'b0111.
    check_y7_decode: assert property (
        @(posedge clk) Y[7] == ((~A[3]) & A[2] & A[1] & A[0])
    );

    // Y[8] decodes input value 4'b1000.
    check_y8_decode: assert property (
        @(posedge clk) Y[8] == (A[3] & (~A[2]) & (~A[1]) & (~A[0]))
    );

    // Y[9] decodes input value 4'b1001.
    check_y9_decode: assert property (
        @(posedge clk) Y[9] == (A[3] & (~A[2]) & (~A[1]) & A[0])
    );

    // Y[10] decodes input value 4'b1010.
    check_y10_decode: assert property (
        @(posedge clk) Y[10] == (A[3] & (~A[2]) & A[1] & (~A[0]))
    );

    // Y[11] decodes input value 4'b1011.
    check_y11_decode: assert property (
        @(posedge clk) Y[11] == (A[3] & (~A[2]) & A[1] & A[0])
    );

    // Y[12] decodes input value 4'b1100.
    check_y12_decode: assert property (
        @(posedge clk) Y[12] == (A[3] & A[2] & (~A[1]) & (~A[0]))
    );

    // Y[13] decodes input value 4'b1101.
    check_y13_decode: assert property (
        @(posedge clk) Y[13] == (A[3] & A[2] & (~A[1]) & A[0])
    );

    // Y[14] decodes input value 4'b1110.
    check_y14_decode: assert property (
        @(posedge clk) Y[14] == (A[3] & A[2] & A[1] & (~A[0]))
    );

    // Y[15] decodes input value 4'b1111.
    check_y15_decode: assert property (
        @(posedge clk) Y[15] == (A[3] & A[2] & A[1] & A[0])
    );

    // The decoder output is always one-hot.
    check_y_onehot: assert property (
        @(posedge clk) $onehot(Y)
    );

    // The full output bus matches a 4-to-16 one-hot decode.
    check_y_full_decode: assert property (
        @(posedge clk) Y == (16'h0001 << A)
    );

endmodule