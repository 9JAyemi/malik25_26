module decoder_4to16_pipeline_assertions (
    input logic [1:0]  select,
    input logic        en,
    input logic        clk,
    input logic [15:0] out
);

    localparam [15:0] DEC_DISABLED = 16'hFFFF;
    localparam [15:0] DEC_SEL_00   = 16'hFFFE;
    localparam [15:0] DEC_SEL_01   = 16'hFFFD;
    localparam [15:0] DEC_SEL_10   = 16'hFFFB;
    localparam [15:0] DEC_SEL_11   = 16'hFFF7;

    // High enable drives all outputs high after the pipeline delay.
    check_enable_high_all_ones: assert property (
        @(posedge clk) en |-> ##2 (out == DEC_DISABLED)
    );

    // Low enable with select 00 clears bit 0 after the pipeline delay.
    check_decode_select_00: assert property (
        @(posedge clk) (!en && (select == 2'b00)) |-> ##2 (out == DEC_SEL_00)
    );

    // Low enable with select 01 clears bit 1 after the pipeline delay.
    check_decode_select_01: assert property (
        @(posedge clk) (!en && (select == 2'b01)) |-> ##2 (out == DEC_SEL_01)
    );

    // Low enable with select 10 clears bit 2 after the pipeline delay.
    check_decode_select_10: assert property (
        @(posedge clk) (!en && (select == 2'b10)) |-> ##2 (out == DEC_SEL_10)
    );

    // Low enable with select 11 clears bit 3 after the pipeline delay.
    check_decode_select_11: assert property (
        @(posedge clk) (!en && (select == 2'b11)) |-> ##2 (out == DEC_SEL_11)
    );

    // The upper 12 output bits are always high once the pipeline response appears.
    check_upper_bits_always_high: assert property (
        @(posedge clk) 1'b1 |-> ##2 (out[15:4] == 12'hFFF)
    );

    // Low enable produces exactly one active-low bit in the low nibble.
    check_low_enable_active_low_onehot: assert property (
        @(posedge clk) !en |-> ##2 ($onehot(~out[3:0]))
    );

    // Output is always one of the RTL-assigned encodings after the pipeline delay.
    check_output_encoding_legal: assert property (
        @(posedge clk) 1'b1 |-> ##2 (
            (out == DEC_DISABLED) ||
            (out == DEC_SEL_00)   ||
            (out == DEC_SEL_01)   ||
            (out == DEC_SEL_10)   ||
            (out == DEC_SEL_11)
        )
    );

endmodule