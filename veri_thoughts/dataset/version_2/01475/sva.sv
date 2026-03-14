module decoder_3to8_sva (
    input logic clk,
    input logic [2:0] in,
    input logic en,
    input logic [7:0] out
);
    ///// Decoder correctness /////
    // When disabled, all outputs must be 0.
    check_out_zero_when_disabled: assert property (
        @(posedge clk) (en == 1'b0) |-> (out == 8'b00000000)
    );

    // When enabled, output must be non-zero.
    check_out_nonzero_when_enabled: assert property (
        @(posedge clk) (en == 1'b1) |-> (out != 8'b00000000)
    );

    // When enabled, output must be one-hot.
    check_onehot_when_enabled: assert property (
        @(posedge clk) (en == 1'b1) |-> $onehot(out)
    );

    // When enabled and in==000, out must be 00000001.
    check_decode_case_0: assert property (
        @(posedge clk) (en == 1'b1 && in == 3'b000) |-> (out == 8'b00000001)
    );

    // When enabled and in==001, out must be 00000010.
    check_decode_case_1: assert property (
        @(posedge clk) (en == 1'b1 && in == 3'b001) |-> (out == 8'b00000010)
    );

    // When enabled and in==010, out must be 00000100.
    check_decode_case_2: assert property (
        @(posedge clk) (en == 1'b1 && in == 3'b010) |-> (out == 8'b00000100)
    );

    // When enabled and in==011, out must be 00001000.
    check_decode_case_3: assert property (
        @(posedge clk) (en == 1'b1 && in == 3'b011) |-> (out == 8'b00001000)
    );

    // When enabled and in==100, out must be 00010000.
    check_decode_case_4: assert property (
        @(posedge clk) (en == 1'b1 && in == 3'b100) |-> (out == 8'b00010000)
    );

    // When enabled and in==101, out must be 00100000.
    check_decode_case_5: assert property (
        @(posedge clk) (en == 1'b1 && in == 3'b101) |-> (out == 8'b00100000)
    );

    // When enabled and in==110, out must be 01000000.
    check_decode_case_6: assert property (
        @(posedge clk) (en == 1'b1 && in == 3'b110) |-> (out == 8'b01000000)
    );

    // When enabled and in==111, out must be 10000000.
    check_decode_case_7: assert property (
        @(posedge clk) (en == 1'b1 && in == 3'b111) |-> (out == 8'b10000000)
    );

    // If any output bit is high, enable must be high.
    check_out_high_implies_enabled: assert property (
        @(posedge clk) (|out) |-> (en == 1'b1)
    );

    // When enabled, the bit at index 'in' must be high.
    check_selected_bit_high_when_enabled: assert property (
        @(posedge clk) (en == 1'b1) |-> (out[in] == 1'b1)
    );
endmodule