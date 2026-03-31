module bin2gray_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] gray
);

// gray[3] mirrors binary[3].
    check_gray3_mirrors_binary3: assert property (
        @(posedge clk) gray[3] == binary[3]
    );

// gray[2] is binary[3] XOR binary[2].
    check_gray2_is_binary3_xor_binary2: assert property (
        @(posedge clk) gray[2] == (binary[3] ^ binary[2])
    );

// gray[1] is binary[2] XOR binary[1].
    check_gray1_is_binary2_xor_binary1: assert property (
        @(posedge clk) gray[1] == (binary[2] ^ binary[1])
    );

// gray[0] is binary[1] XOR binary[0].
    check_gray0_is_binary1_xor_binary0: assert property (
        @(posedge clk) gray[0] == (binary[1] ^ binary[0])
    );

// The full gray vector matches the implemented binary-to-Gray conversion.
    check_full_gray_vector: assert property (
        @(posedge clk) gray == { (binary[3] ^ binary[2]), (binary[2] ^ binary[1]), (binary[1] ^ binary[0]), binary[3] }
    );

endmodule
