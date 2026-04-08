module Immediate_Extend_sva (
    input logic        clk,
    input logic [31:0] data_out,
    input logic [2:0]  load,
    input logic [15:0] data_in
);

    // The RTL always drives a 16-bit value that is zero-extended to 32 bits.
    check_upper_half_zero: assert property (
        @(posedge clk) data_out[31:16] == 16'h0000
    );

    // load 0 places a sign-replicated byte in the low 16 bits.
    check_load0_byte_sign_extend: assert property (
        @(posedge clk)
        (load == 3'd0) |-> (data_out == {16'h0000, {8{data_in[7]}}, data_in[7:0]})
    );

    // load 1 places a sign-replicated nibble in the low 16 bits.
    check_load1_nibble_sign_extend: assert property (
        @(posedge clk)
        (load == 3'd1) |-> (data_out == {16'h0000, {12{data_in[3]}}, data_in[3:0]})
    );

    // load 2 places a sign-replicated 11-bit field in the low 16 bits.
    check_load2_eleven_bit_sign_extend: assert property (
        @(posedge clk)
        (load == 3'd2) |-> (data_out == {16'h0000, {5{data_in[10]}}, data_in[10:0]})
    );

    // load 3 zero-extends data_in[3:0] into data_out.
    check_load3_nibble_zero_extend: assert property (
        @(posedge clk)
        (load == 3'd3) |-> (data_out == {28'b0, data_in[3:0]})
    );

    // load 4 zero-extends data_in[7:0] into data_out.
    check_load4_byte_zero_extend: assert property (
        @(posedge clk)
        (load == 3'd4) |-> (data_out == {24'b0, data_in[7:0]})
    );

    // load 5 places a sign-replicated 5-bit field in the low 16 bits.
    check_load5_five_bit_sign_extend: assert property (
        @(posedge clk)
        (load == 3'd5) |-> (data_out == {16'h0000, {11{data_in[4]}}, data_in[4:0]})
    );

    // load 6 or 7 places data_in[4:2] in the low three bits.
    check_load67_extract_bits_4_to_2: assert property (
        @(posedge clk)
        ((load == 3'd6) || (load == 3'd7)) |-> (data_out == {29'b0, data_in[4:2]})
    );

endmodule