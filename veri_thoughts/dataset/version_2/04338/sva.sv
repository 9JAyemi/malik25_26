module decoder_4to16_sva (
    input logic [3:0]  in,
    input logic        clk,
    input logic [15:0] out
);

    function automatic logic [15:0] decode_expected(input logic [3:0] val);
        begin
            case (val)
                4'h1:    decode_expected = 16'h0001;
                4'h2:    decode_expected = 16'h0002;
                4'h3:    decode_expected = 16'h0004;
                4'h4:    decode_expected = 16'h0008;
                4'h5:    decode_expected = 16'h0010;
                4'h6:    decode_expected = 16'h0020;
                4'h7:    decode_expected = 16'h0040;
                4'h8:    decode_expected = 16'h0080;
                4'h9:    decode_expected = 16'h0100;
                4'hA:    decode_expected = 16'h0200;
                4'hB:    decode_expected = 16'h0400;
                4'hC:    decode_expected = 16'h0800;
                4'hD:    decode_expected = 16'h1000;
                4'hE:    decode_expected = 16'h2000;
                4'hF:    decode_expected = 16'h4000;
                default: decode_expected = 16'h0000;
            endcase
        end
    endfunction

    // Output matches the decode of the input from two clocks earlier.
    check_two_cycle_decode: assert property (
        @(posedge clk) disable iff ($initstate || $past($initstate))
            out == decode_expected($past(in, 2))
    );

    // An input of zero decodes to all zeros two clocks later.
    check_zero_input_maps_to_zero: assert property (
        @(posedge clk) disable iff ($initstate || $past($initstate))
            ($past(in, 2) == 4'h0) |-> (out == 16'h0000)
    );

    // Any nonzero input decodes to exactly one active bit in out[14:0].
    check_nonzero_input_is_onehot: assert property (
        @(posedge clk) disable iff ($initstate || $past($initstate))
            ($past(in, 2) != 4'h0) |-> (!out[15] && $onehot(out[14:0]))
    );

    // Input value 1 maps to the least-significant output bit.
    check_input_one_maps_to_lsb: assert property (
        @(posedge clk) disable iff ($initstate || $past($initstate))
            ($past(in, 2) == 4'h1) |-> (out == 16'h0001)
    );

    // Input value F maps to bit 14 and never to bit 15.
    check_input_f_maps_to_bit14: assert property (
        @(posedge clk) disable iff ($initstate || $past($initstate))
            ($past(in, 2) == 4'hF) |-> (out == 16'h4000)
    );

endmodule