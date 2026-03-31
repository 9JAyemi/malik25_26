module bin2gray_sva (
    input  logic        clk,
    input  logic [3:0]  binary,
    input  logic [3:0]  gray
);
    ///// Functional mapping /////
    // MSB mapping: gray[3] equals binary[3].
    check_gray_bit3_mapping: assert property (
        @(posedge clk) disable iff (1'b0) gray[3] === binary[3]
    );

    // gray[2] is binary[3] XOR binary[2].
    check_gray_bit2_mapping: assert property (
        @(posedge clk) disable iff (1'b0) gray[2] === (binary[3] ^ binary[2])
    );

    // gray[1] is binary[2] XOR binary[1].
    check_gray_bit1_mapping: assert property (
        @(posedge clk) disable iff (1'b0) gray[1] === (binary[2] ^ binary[1])
    );

    // gray[0] is binary[1] XOR binary[0].
    check_gray_bit0_mapping: assert property (
        @(posedge clk) disable iff (1'b0) gray[0] === (binary[1] ^ binary[0])
    );

    // Full vector mapping matches {b3, b3^b2, b2^b1, b1^b0}.
    check_gray_full_mapping: assert property (
        @(posedge clk) disable iff (1'b0) gray === {binary[3], (binary[3]^binary[2]), (binary[2]^binary[1]), (binary[1]^binary[0])}
    );

    ///// Stability /////
    // If binary is stable between cycles, gray must be stable.
    check_gray_stability: assert property (
        @(posedge clk) disable iff (1'b0) $stable(binary) |-> $stable(gray)
    );

    ///// Single-bit input toggle effects /////
    // Only b3 toggles: g3 and g2 toggle; g1 and g0 stay stable.
    check_only_b3_toggles: assert property (
        @(posedge clk) disable iff (1'b0)
            ($changed(binary[3]) && $stable(binary[2]) && $stable(binary[1]) && $stable(binary[0]))
            |-> ($changed(gray[3]) && $changed(gray[2]) && $stable(gray[1]) && $stable(gray[0]))
    );

    // Only b2 toggles: g2 and g1 toggle; g3 and g0 stay stable.
    check_only_b2_toggles: assert property (
        @(posedge clk) disable iff (1'b0)
            ($changed(binary[2]) && $stable(binary[3]) && $stable(binary[1]) && $stable(binary[0]))
            |-> ($changed(gray[2]) && $changed(gray[1]) && $stable(gray[3]) && $stable(gray[0]))
    );

    // Only b1 toggles: g1 and g0 toggle; g3 and g2 stay stable.
    check_only_b1_toggles: assert property (
        @(posedge clk) disable iff (1'b0)
            ($changed(binary[1]) && $stable(binary[3]) && $stable(binary[2]) && $stable(binary[0]))
            |-> ($changed(gray[1]) && $changed(gray[0]) && $stable(gray[3]) && $stable(gray[2]))
    );

    // Only b0 toggles: only g0 toggles; g3,g2,g1 stay stable.
    check_only_b0_toggles: assert property (
        @(posedge clk) disable iff (1'b0)
            ($changed(binary[0]) && $stable(binary[3]) && $stable(binary[2]) && $stable(binary[1]))
            |-> ($changed(gray[0]) && $stable(gray[3]) && $stable(gray[2]) && $stable(gray[1]))
    );
endmodule