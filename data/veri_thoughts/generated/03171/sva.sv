module binary_splitter_and_multiplexer_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [2:0]  select,
    input logic [7:0]  final_output,
    input logic [2:0]  outv,
    input logic        o2,
    input logic        o1,
    input logic        o0,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // out_hi is the upper byte of in.
    check_out_hi_split: assert property (
        @(posedge clk) out_hi == in[15:8]
    );

    // out_lo is the lower byte of in.
    check_out_lo_split: assert property (
        @(posedge clk) out_lo == in[7:0]
    );

    // outv directly mirrors select.
    check_outv_matches_select: assert property (
        @(posedge clk) outv == select
    );

    // o2, o1, and o0 directly mirror the select bits.
    check_select_bit_outputs: assert property (
        @(posedge clk) {o2, o1, o0} == select
    );

    // final_output keeps select in its low three bits.
    check_final_output_low_bits: assert property (
        @(posedge clk) final_output[2:0] == select
    );

    // For select 000, the upper bits carry out_hi[4:0].
    check_final_output_upper_sel_000: assert property (
        @(posedge clk) (select == 3'b000) |-> (final_output[7:3] == in[12:8])
    );

    // For select 001, the upper bits carry out_hi[5:1].
    check_final_output_upper_sel_001: assert property (
        @(posedge clk) (select == 3'b001) |-> (final_output[7:3] == in[13:9])
    );

    // For select 010, the upper bits carry out_hi[6:2].
    check_final_output_upper_sel_010: assert property (
        @(posedge clk) (select == 3'b010) |-> (final_output[7:3] == in[14:10])
    );

    // For select 011, the upper bits carry out_hi[7:3].
    check_final_output_upper_sel_011: assert property (
        @(posedge clk) (select == 3'b011) |-> (final_output[7:3] == in[15:11])
    );

    // For select 100, the upper bits are zero-extended out_hi[7:4].
    check_final_output_upper_sel_100: assert property (
        @(posedge clk) (select == 3'b100) |-> (final_output[7:3] == {1'b0, in[15:12]})
    );

    // For select 101, the upper bits are zero-extended out_hi[7:5].
    check_final_output_upper_sel_101: assert property (
        @(posedge clk) (select == 3'b101) |-> (final_output[7:3] == {2'b00, in[15:13]})
    );

    // For select 110, the upper bits are zero-extended out_hi[7:6].
    check_final_output_upper_sel_110: assert property (
        @(posedge clk) (select == 3'b110) |-> (final_output[7:3] == {3'b000, in[15:14]})
    );

    // For select 111, the upper bits are zero-extended out_hi[7].
    check_final_output_upper_sel_111: assert property (
        @(posedge clk) (select == 3'b111) |-> (final_output[7:3] == {4'b0000, in[15]})
    );

endmodule