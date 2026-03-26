module ones_complement_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] ones_comp
);

    // Output is always the bitwise inverse of the input.
    check_output_matches_inverse: assert property (
        @(posedge clk) ones_comp == ~binary
    );

    // Output bit 0 is the inverse of input bit 0.
    check_bit0_inverse: assert property (
        @(posedge clk) ones_comp[0] == ~(binary[0])
    );

    // Output bit 1 is the inverse of input bit 1.
    check_bit1_inverse: assert property (
        @(posedge clk) ones_comp[1] == ~(binary[1])
    );

    // Output bit 2 is the inverse of input bit 2.
    check_bit2_inverse: assert property (
        @(posedge clk) ones_comp[2] == ~(binary[2])
    );

    // Output bit 3 is the inverse of input bit 3.
    check_bit3_inverse: assert property (
        @(posedge clk) ones_comp[3] == ~(binary[3])
    );

endmodule