module gray_code_converter_sva (
    input logic [3:0] data_in,
    input logic [3:0] gray_out
);

    // Purely combinational RTL with no explicit clock or reset; sample on $global_clock.

    // Output bit 0 directly mirrors input bit 0.
    check_gray_bit0_passthrough: assert property (
        @($global_clock) gray_out[0] === data_in[0]
    );

    // Output bit 1 directly mirrors input bit 1.
    check_gray_bit1_passthrough: assert property (
        @($global_clock) gray_out[1] === data_in[1]
    );

    // Output bit 2 is the XOR of input bits 2 and 0.
    check_gray_bit2_xor: assert property (
        @($global_clock) gray_out[2] === (data_in[2] ^ data_in[0])
    );

    // Output bit 3 is the XOR of input bits 3 and 1.
    check_gray_bit3_xor: assert property (
        @($global_clock) gray_out[3] === (data_in[3] ^ data_in[1])
    );

    // Full output matches the RTL's two-stage combinational expansion.
    check_gray_full_mapping: assert property (
        @($global_clock) gray_out === {data_in[3] ^ data_in[1], data_in[2] ^ data_in[0], data_in[1], data_in[0]}
    );

    // Stable input must keep the output stable.
    check_stable_input_stable_output: assert property (
        @($global_clock) $stable(data_in) |-> $stable(gray_out)
    );

    // A change only on input bit 0 cannot affect output bits 1 or 3.
    check_bit0_change_independence: assert property (
        @($global_clock)
        ($changed(data_in[0]) && $stable(data_in[1]) && $stable(data_in[2]) && $stable(data_in[3]))
        |-> ($stable(gray_out[1]) && $stable(gray_out[3]))
    );

    // A change only on input bit 1 cannot affect output bits 0 or 2.
    check_bit1_change_independence: assert property (
        @($global_clock)
        ($changed(data_in[1]) && $stable(data_in[0]) && $stable(data_in[2]) && $stable(data_in[3]))
        |-> ($stable(gray_out[0]) && $stable(gray_out[2]))
    );

    // A change only on input bit 2 cannot affect output bits 0, 1, or 3.
    check_bit2_change_independence: assert property (
        @($global_clock)
        ($changed(data_in[2]) && $stable(data_in[0]) && $stable(data_in[1]) && $stable(data_in[3]))
        |-> ($stable(gray_out[0]) && $stable(gray_out[1]) && $stable(gray_out[3]))
    );

    // A change only on input bit 3 cannot affect output bits 0, 1, or 2.
    check_bit3_change_independence: assert property (
        @($global_clock)
        ($changed(data_in[3]) && $stable(data_in[0]) && $stable(data_in[1]) && $stable(data_in[2]))
        |-> ($stable(gray_out[0]) && $stable(gray_out[1]) && $stable(gray_out[2]))
    );

endmodule