module parity_checker_sva (
    input logic [7:0] data_in,
    input logic       sel_b1,
    input logic       parity
);

    // When sel_b1 is low, parity matches the input XOR.
    check_parity_low_sel: assert property (
        @($global_clock) (!sel_b1) |-> (parity == (data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]))
    );

    // When sel_b1 is high, parity is the inverted input XOR.
    check_parity_high_sel: assert property (
        @($global_clock) sel_b1 |-> (parity == ~(data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]))
    );

    // Parity always matches the selected output function.
    check_parity_function: assert property (
        @($global_clock) parity == (sel_b1 ? ~(data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]) : (data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]))
    );

endmodule