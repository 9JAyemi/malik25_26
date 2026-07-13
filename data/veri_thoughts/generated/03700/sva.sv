module data_module_sva #(
    parameter [7:0] MASK_AND = 8'hF0,
    parameter [7:0] MASK_OR  = 8'h0F,
    parameter [7:0] MASK_XOR = 8'h55
) (
    input logic [7:0] data_in,
    input logic [3:0] selector,
    input logic [7:0] data_out
);

    // No DUT clock or reset; sample combinational behavior on the formal global clock.

    // Selector 0 passes data_in through unchanged.
    check_selector_identity: assert property (
        @($global_clock) (selector == 4'h0) |-> (data_out == data_in)
    );

    // Selector 1 outputs the bitwise inverse of data_in.
    check_selector_invert: assert property (
        @($global_clock) (selector == 4'h1) |-> (data_out == ~data_in)
    );

    // Selector 2 shifts data_in left by one and inserts 0 in the LSB.
    check_selector_shift_left: assert property (
        @($global_clock) (selector == 4'h2) |-> (data_out == {data_in[6:0], 1'b0})
    );

    // Selector 3 shifts data_in right by one and inserts 0 in the MSB.
    check_selector_shift_right: assert property (
        @($global_clock) (selector == 4'h3) |-> (data_out == {1'b0, data_in[7:1]})
    );

    // Selector 4 ANDs data_in with MASK_AND.
    check_selector_and_mask: assert property (
        @($global_clock) (selector == 4'h4) |-> (data_out == (data_in & MASK_AND))
    );

    // Selector 5 ORs data_in with MASK_OR.
    check_selector_or_mask: assert property (
        @($global_clock) (selector == 4'h5) |-> (data_out == (data_in | MASK_OR))
    );

    // Selector 6 XORs data_in with MASK_XOR.
    check_selector_xor_mask: assert property (
        @($global_clock) (selector == 4'h6) |-> (data_out == (data_in ^ MASK_XOR))
    );

    // Selector 7 outputs the two's complement of data_in.
    check_selector_twos_complement: assert property (
        @($global_clock) (selector == 4'h7) |-> (data_out == ((~data_in) + 8'h01))
    );

    // Selectors 8 through F use the default pass-through behavior.
    check_selector_default_passthrough: assert property (
        @($global_clock) selector[3] |-> (data_out == data_in)
    );

endmodule