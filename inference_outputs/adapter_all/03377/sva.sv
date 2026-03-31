module hex_display_sva #(
    parameter INVERT = 0
)
(
    input logic [3:0] in,
    input logic       enable,
    input logic [6:0] out
);

    // Output matches the enabled hex encoding.
    check_hex_encoding: assert property (
        @($global_clock)
        out == (enable ? ({
            4'h0: 7'b0111111,
            4'h1: 7'b0000110,
            4'h2: 7'b1011011,
            4'h3: 7'b1001111,
            4'h4: 7'b1100110,
            4'h5: 7'b1101101,
            4'h6: 7'b1111101,
            4'h7: 7'b0000111,
            4'h8: 7'b1111111,
            4'h9: 7'b1101111,
            4'ha: 7'b1110111,
            4'hb: 7'b1111100,
            4'hc: 7'b0111001,
            4'hd: 7'b1011110,
            4'he: 7'b1111001,
            4'hf: 7'b1110001
        }[in]) : 7'b0000000)
    );

    // Output is always either the enabled hex code or zero.
    check_output_zero_or_hex: assert property (
        @($global_clock)
        out == (enable ? ({
            4'h0: 7'b0111111,
            4'h1: 7'b0000110,
            4'h2: 7'b1011011,
            4'h3: 7'b1001111,
            4'h4: 7'b1100110,
            4'h5: 7'b1101101,
            4'h6: 7'b1111101,
            4'h7: 7'b0000111,
            4'h8: 7'b1111111,
            4'h9: 7'b1101111,
            4'ha: 7'b1110111,
            4'hb: 7'b1111100,
            4'hc: 7'b0111001,
            4'hd: 7'b1011110,
            4'he: 7'b1111001,
            4'hf: 7'b1110001
        }[in]) : 7'b0000000)
    );

    // When disabled, the output is zero.
    check_disable_clears_output: assert property (
        @($global_clock)
        !enable |-> (out == 7'b0000000)
    );

    // When enabled, the output is one of the valid hex patterns.
    check_enable_selects_valid_hex: assert property (
        @($global_clock)
        enable |-> (
            out == 7'b0111111 ||
            out == 7'b0000110 ||
            out == 7'b1011011 ||
            out == 7'b1001111 ||
            out == 7'b1100110 ||
            out == 7'b1101101 ||
            out == 7'b1111101 ||
            out == 7'b0000111 ||
            out == 7'b1111111 ||
            out == 7'b1101111 ||
            out == 7'b1110111 ||
            out == 7'b1111100 ||
            out == 7'b0111001 ||
            out == 7'b1011110 ||
            out == 7'b1111001 ||
            out == 7'b1110001
        )
    );

    // Inverted mode drives the inverted hex encoding.
    check_inverted_hex_encoding: assert property (
        @($global_clock)
        INVERT |-> (out == ~({
            4'h0: 7'b0111111,
            4'h1: 7'b0000110,
            4'h2: 7'b1011011,
            4'h3: 7'b1001111,
            4'h4: 7'b1100110,
            4'h5: 7'b1101101,
            4'h6: 7'b1111101,
            4'h7: 7'b0000111,
            4'h8: 7'b1111111,
            4'h9: 7'b1101111,
            4'ha: 7'b1110111,
            4'hb: 7'b1111100,
            4'hc: 7'b0111001,
            4'hd: 7'b1011110,
            4'he: 7'b1111001,
            4'hf: 7'b1110001
        }[in]))
    );

    // Inverted mode still forces zero when disabled.
    check_inverted_disable_clears_output: assert property (
        @($global_clock)
        INVERT && !enable |-> (out == 7'b0000000)
    );

    // Inverted mode still restricts the output to valid hex patterns.
    check_inverted_enable_selects_valid_hex: assert property (
        @($global_clock)
        INVERT && enable |-> (
            out == ~7'b0111111 ||
            out == ~7'b0000110 ||
            out == ~7'b1011011 ||
            out == ~7'b1001111 ||
            out == ~7'b1100110 ||
            out == ~7'b1101101 ||
            out == ~7'b1111101 ||
            out == ~7'b0000111 ||
            out == ~7'b1111111 ||
            out == ~7'b1101111 ||
            out == ~7'b1110111 ||
            out == ~7'b1111100 ||
            out == ~7'b0111001 ||
            out == ~7'b1011110 ||
            out == ~7'b1111001 ||
            out == ~7'b1110001
        )
    );

endmodule