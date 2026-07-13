module twos_complement_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] twos_comp
);

// twos_comp equals bitwise NOT of binary plus 1 (4-bit wrap).
    check_twos_comp_definition: assert property (
        @(posedge clk) twos_comp == ((~binary) + 4'b0001)
    );

// LSB of twos_comp equals XOR of binary LSB and 1.
    check_lsb_xor: assert property (
        @(posedge clk) twos_comp[0] == (binary[0] ^ 1'b1)
    );

// Bit1 of twos_comp equals XOR of binary bit1 and carry from bit0.
    check_bit1_xor_with_carry: assert property (
        @(posedge clk) twos_comp[1] == (binary[1] ^ (binary[0] & 1'b1))
    );

// Bit2 of twos_comp equals XOR of binary bit2 and carry from bit1.
    check_bit2_xor_with_carry: assert property (
        @(posedge clk) twos_comp[2] == (binary[2] ^ ((binary[1] & 1'b1) | (binary[0] & 1'b1)))
    );

// Bit3 of twos_comp equals XOR of binary bit3 and carry from bit2.
    check_bit3_xor_with_carry: assert property (
        @(posedge clk) twos_comp[3] == (binary[3] ^ ((binary[2] & 1'b1) | (binary[1] & 1'b1) | (binary[0] & 1'b1)))
    );

// 0000 maps to 0001.
    check_zero_maps_to_one: assert property (
        @(posedge clk) (binary == 4'b0000) |-> (twos_comp == 4'b0001)
    );

// 0001 maps to 1110.
    check_one_maps_to_e: assert property (
        @(posedge clk) (binary == 4'b0001) |-> (twos_comp == 4'b1110)
    );

// 1111 maps to 0000.
    check_all_ones_maps_to_zero: assert property (
        @(posedge clk) (binary == 4'b1111) |-> (twos_comp == 4'b0000)
    );

endmodule
