module top_module_sva (
    input  logic [1:0]  in,
    input  logic [15:0] out,
    input  logic        select,
    input  logic [3:0]  select_bit,
    input  logic [15:0] decoder_out
);
    // select_bit must encode 1<<in
    check_select_bit_shift: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        select_bit == (4'b0001 << in)
    );

    // select_bit is never zero
    check_select_bit_nonzero: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        select_bit != 4'b0000
    );

    // out equals 1 shifted by select_bit
    check_out_from_select_bit_shift: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        out == (16'h0001 << select_bit)
    );

    // The selected bit of out is 1
    check_out_selected_bit_one: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        out[select_bit] == 1'b1
    );

    // out is exactly one-hot
    check_out_onehot: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        $onehot(out)
    );

    // Only bits {1,2,4,8} can ever be set in out
    check_out_legal_bits_only: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        (out & ~(16'h0002 | 16'h0004 | 16'h0010 | 16'h0100)) == 16'h0000
    );

    // select reflects whether select_bit is non-zero
    check_select_matches_select_bit_nonzero: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        select == (select_bit != 4'b0000)
    );

    // Mapping: in==00 -> out==0x0002
    check_out_map_in_00: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        (in == 2'b00) |-> (out == 16'h0002)
    );

    // Mapping: in==01 -> out==0x0004
    check_out_map_in_01: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        (in == 2'b01) |-> (out == 16'h0004)
    );

    // Mapping: in==10 -> out==0x0010
    check_out_map_in_10: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        (in == 2'b10) |-> (out == 16'h0010)
    );

    // Mapping: in==11 -> out==0x0100
    check_out_map_in_11: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        (in == 2'b11) |-> (out == 16'h0100)
    );

    // decoder_out is exactly one-hot
    check_decoder_out_onehot: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        $onehot(decoder_out)
    );

    // decoder_out equals 1<<in (bits [0..3])
    check_decoder_out_shift: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        decoder_out == (16'h0001 << in)
    );

    // decoder_out upper bits [15:4] are always zero
    check_decoder_out_high_bits_zero: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
        decoder_out[15:4] == 12'h000
    );
endmodule