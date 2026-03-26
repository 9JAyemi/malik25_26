module decoder_2to4_adder_sva (
    input logic       clk,
    input logic [1:0] in,
    input logic       ena,
    input logic       cin,
    input logic [3:0] out,
    input logic       cout
);

    // Two cycles after a low enable is captured, outputs are cleared.
    check_outputs_zero_when_pipelined_enable_low: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) && !$past(ena, 2)) |-> (out == 4'b0000 && cout == 1'b0)
    );

    // With pipelined enable high, out matches the decoder/adder OR result.
    check_out_matches_registered_decoder_or_adder: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) && $past(ena, 2)) |-> (
            out == (
                ($past(ena, 1) ? (4'b0001 << $past(in, 1)) : 4'b0000) |
                {2'b00, ($past(in, 2) + $past(cin, 2))}
            )
        )
    );

    // With pipelined enable high, cout is the carry of the registered add.
    check_cout_matches_registered_add_carry: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) && $past(ena, 2)) |-> (
            cout == (($past(in, 2) == 2'b11) && $past(cin, 2))
        )
    );

    // Decoder select 0 forces out[0] high when the output update is enabled.
    check_decode_sel0_sets_out0: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) &&
         $past(ena, 2) && $past(ena, 1) && ($past(in, 1) == 2'b00)) |-> (out[0] == 1'b1)
    );

    // Decoder select 1 forces out[1] high when the output update is enabled.
    check_decode_sel1_sets_out1: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) &&
         $past(ena, 2) && $past(ena, 1) && ($past(in, 1) == 2'b01)) |-> (out[1] == 1'b1)
    );

    // Decoder select 2 sets only bit 2 in the upper half.
    check_decode_sel2_sets_upper_pattern: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) &&
         $past(ena, 2) && $past(ena, 1) && ($past(in, 1) == 2'b10)) |-> (out[3:2] == 2'b01)
    );

    // Decoder select 3 sets only bit 3 in the upper half.
    check_decode_sel3_sets_upper_pattern: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) &&
         $past(ena, 2) && $past(ena, 1) && ($past(in, 1) == 2'b11)) |-> (out[3:2] == 2'b10)
    );

    // Without an upper-bit decode, the upper output bits remain low.
    check_upper_bits_zero_without_upper_decode: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) && $past(ena, 2) &&
         (!$past(ena, 1) || ($past(in, 1) == 2'b00) || ($past(in, 1) == 2'b01))) |->
        (out[3:2] == 2'b00)
    );

    // Low bits follow the registered add when decoder does not target bits 0 or 1.
    check_low_bits_follow_add_when_no_low_decode: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) && $past(ena, 2) &&
         (!$past(ena, 1) || ($past(in, 1) == 2'b10) || ($past(in, 1) == 2'b11))) |->
        (out[1:0] == ($past(in, 2) + $past(cin, 2)))
    );

endmodule