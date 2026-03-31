module binary_to_gray_sva (
    input logic clk,
    input logic [8:0] binary,
    input logic [3:0] gray
);
    ///// Combinational mapping checks (sampled on clk) /////
    // gray[3] equals binary[8].
    check_gray3_eq_binary8: assert property (
        @(posedge clk) gray[3] == binary[8]
    );
    // gray[2] equals binary[8] XOR binary[7].
    check_gray2_eq_b8_xor_b7: assert property (
        @(posedge clk) gray[2] == (binary[8] ^ binary[7])
    );
    // gray[1] equals binary[7] XOR binary[6].
    check_gray1_eq_b7_xor_b6: assert property (
        @(posedge clk) gray[1] == (binary[7] ^ binary[6])
    );
    // gray[0] equals binary[6] XOR binary[5].
    check_gray0_eq_b6_xor_b5: assert property (
        @(posedge clk) gray[0] == (binary[6] ^ binary[5])
    );

    ///// Sensitivity and stability /////
    // If binary[8:5] is stable, gray must be stable.
    check_gray_stable_when_upper_bits_stable: assert property (
        @(posedge clk) $stable(binary[8:5]) |-> $stable(gray)
    );
    // If gray changes, at least one of binary[8:5] changed.
    check_gray_change_requires_upper_bit_change: assert property (
        @(posedge clk) $changed(gray) |-> $changed({binary[8],binary[7],binary[6],binary[5]})
    );

    ///// Single-bit change effects /////
    // If only binary[8] changes (others [7:5] stable), gray[3] and gray[2] change; gray[1:0] stay.
    check_singlebit_b8_change_effects: assert property (
        @(posedge clk) ($changed(binary[8]) && $stable(binary[7:5])) |-> ($changed(gray[3]) && $changed(gray[2]) && $stable(gray[1:0]))
    );
    // If only binary[7] changes, gray[2] and gray[1] change; gray[3] and gray[0] stay.
    check_singlebit_b7_change_effects: assert property (
        @(posedge clk) ($changed(binary[7]) && $stable(binary[8]) && $stable(binary[6:5])) |-> ($changed(gray[2]) && $changed(gray[1]) && $stable(gray[3]) && $stable(gray[0]))
    );
    // If only binary[6] changes, gray[1] and gray[0] change; gray[3:2] stay.
    check_singlebit_b6_change_effects: assert property (
        @(posedge clk) ($changed(binary[6]) && $stable(binary[8:7]) && $stable(binary[5])) |-> ($changed(gray[1]) && $changed(gray[0]) && $stable(gray[3:2]))
    );
    // If only binary[5] changes, only gray[0] changes; gray[3:1] stay.
    check_singlebit_b5_change_effects: assert property (
        @(posedge clk) ($changed(binary[5]) && $stable(binary[8:6])) |-> ($changed(gray[0]) && $stable(gray[3:1]))
    );
endmodule