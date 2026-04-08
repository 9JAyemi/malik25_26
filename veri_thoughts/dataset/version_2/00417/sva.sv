module memoryProtection_assertions #(
    parameter n = 8,
    parameter m = 4
) (
    input logic [n-1:0] addr,
    input logic [m-1:0] cs
);

    // cs[0] must be the inverse of the block1 address decode.
    check_cs0_block1_decode: assert property (
        @($global_clock) cs[0] === ~((addr[0] == 1'b1) & (addr[1] == 1'b0))
    );

    // cs[1] must be the inverse of the block2 address decode.
    check_cs1_block2_decode: assert property (
        @($global_clock) cs[1] === ~((addr[2] == 1'b1) | (addr[3] == 1'b1))
    );

    // cs[2] must be the inverse of the block3 address decode.
    check_cs2_block3_decode: assert property (
        @($global_clock) cs[2] === ~((addr[4] == 1'b0) & (addr[5] == 1'b0) & (addr[6] == 1'b0))
    );

    // cs[3] must be the inverse of the block4 address decode.
    check_cs3_block4_decode: assert property (
        @($global_clock) cs[3] === ~(addr[7] == 1'b1)
    );

endmodule