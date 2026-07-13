module signed_mag_to_twos_comp_sva (
    input logic       clk,
    input logic [3:0] signed_mag,
    input logic [3:0] twos_comp
);

    // Output matches the implemented conversion function.
    check_full_mapping: assert property (
        @(posedge clk)
        twos_comp == (signed_mag[3] ? ((~signed_mag) + 4'b0001) : signed_mag)
    );

    // Non-negative inputs pass through unchanged.
    check_nonnegative_passthrough: assert property (
        @(posedge clk)
        !signed_mag[3] |-> (twos_comp == signed_mag)
    );

    // Negative inputs use bitwise invert plus one on all four bits.
    check_negative_invert_plus_one: assert property (
        @(posedge clk)
        signed_mag[3] |-> (twos_comp == ((~signed_mag) + 4'b0001))
    );

endmodule