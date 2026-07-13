module binary_to_gray_sva (
    input logic clk,
    input logic [8:0] binary,
    input logic [3:0] gray
);

// gray[3] must equal binary[8].
    check_gray3_matches_binary8: assert property (
        @(posedge clk) gray[3] == binary[8]
    );

// gray[2] must equal binary[8] XOR binary[7].
    check_gray2_matches_binary8_xor7: assert property (
        @(posedge clk) gray[2] == (binary[8] ^ binary[7])
    );

// gray[1] must equal binary[7] XOR binary[6].
    check_gray1_matches_binary7_xor6: assert property (
        @(posedge clk) gray[1] == (binary[7] ^ binary[6])
    );

// gray[0] must equal binary[6] XOR binary[5].
    check_gray0_matches_binary6_xor5: assert property (
        @(posedge clk) gray[0] == (binary[6] ^ binary[5])
    );

endmodule
