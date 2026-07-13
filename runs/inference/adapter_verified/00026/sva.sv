module bin2gray_sva (
    input logic clk,
    input logic [3:0] bin,
    input logic [3:0] gray
);

// gray[3] mirrors bin[3].
    check_gray3_mirrors_bin3: assert property (
        @(posedge clk) gray[3] == bin[3]
    );

// gray[2] is bin[3] XOR bin[2].
    check_gray2_is_bin3_xor_bin2: assert property (
        @(posedge clk) gray[2] == (bin[3] ^ bin[2])
    );

// gray[1] is bin[2] XOR bin[1].
    check_gray1_is_bin2_xor_bin1: assert property (
        @(posedge clk) gray[1] == (bin[2] ^ bin[1])
    );

// gray[0] is bin[1] XOR bin[0].
    check_gray0_is_bin1_xor_bin0: assert property (
        @(posedge clk) gray[0] == (bin[1] ^ bin[0])
    );

// The full gray vector matches the RTL bit equations.
    check_full_gray_vector: assert property (
        @(posedge clk) gray == { (bin[3] ^ bin[2]), (bin[2] ^ bin[1]), (bin[1] ^ bin[0]), bin[3] }
    );

endmodule
