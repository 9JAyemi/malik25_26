module AddThree_sva (
    (* gclk *) input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);

    // Output always equals input plus three.
    check_add_three_function: assert property (
        @(posedge clk) out == (in + 4'b0011)
    );

    // Bit 0 inverts when adding three.
    check_out_bit0: assert property (
        @(posedge clk) out[0] == ~in[0]
    );

    // Bit 1 includes the carry from bit 0.
    check_out_bit1: assert property (
        @(posedge clk) out[1] == ~(in[1] ^ in[0])
    );

    // Bit 2 includes carry propagation from the low bits.
    check_out_bit2: assert property (
        @(posedge clk) out[2] == (in[2] ^ (in[1] | in[0]))
    );

    // Bit 3 includes carry propagation into the MSB.
    check_out_bit3: assert property (
        @(posedge clk) out[3] == (in[3] ^ (in[2] & (in[1] | in[0])))
    );

endmodule