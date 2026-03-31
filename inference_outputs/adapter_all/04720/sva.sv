module functional_module_sva (
    input logic [3:0] B,
    input logic [1:0] in,
    input logic [15:0] out
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // out must always be one-hot.
    check_out_onehot: assert property (
        @($global_clock) $onehot(out)
    );

    // in=00 selects bit 0 of the shifted result.
    check_decode_in00: assert property (
        @($global_clock) (in == 2'b00) |-> (out == (16'h0001 << (B + 4'b0011)))
    );

    // in=01 selects bit 1 of the shifted result.
    check_decode_in01: assert property (
        @($global_clock) (in == 2'b01) |-> (out == (16'h0002 << (B + 4'b0100)))
    );

    // in=10 selects bit 2 of the shifted result.
    check_decode_in10: assert property (
        @($global_clock) (in == 2'b10) |-> (out == (16'h0004 << (B + 4'b0101)))
    );

    // in=11 selects bit 3 of the shifted result.
    check_decode_in11: assert property (
        @($global_clock) (in == 2'b11) |-> (out == (16'h0008 << (B + 4'b0110)))
    );

    // The selected bit must be the only asserted bit in out.
    check_selected_bit_only: assert property (
        @($global_clock)
        out == (16'h0001 << (B + 4'b0011)) ||
        out == (16'h0002 << (B + 4'b0100)) ||
        out == (16'h0004 << (B + 4'b0101)) ||
        out == (16'h0008 << (B + 4'b0110))
    );

    // Stable inputs must keep the combinational output stable.
    check_stable_inputs_hold_output: assert property (
        @($global_clock) ($stable(B) && $stable(in)) |-> $stable(out)
    );

endmodule