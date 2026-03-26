module top_module_sva (
    input logic [7:0] in,
    input logic       sel,
    input logic [2:0] pos,
    input logic [7:0] out_always
);

    // Bit 7 has highest priority.
    check_pos_from_bit7: assert property (
        @(posedge sel) in[7] |-> (pos == 3'd7)
    );

    // Bit 6 is selected when bit 7 is clear.
    check_pos_from_bit6: assert property (
        @(posedge sel) ((!in[7]) && in[6]) |-> (pos == 3'd6)
    );

    // Bit 5 is selected when bits 7:6 are clear.
    check_pos_from_bit5: assert property (
        @(posedge sel) ((in[7:6] == 2'b00) && in[5]) |-> (pos == 3'd5)
    );

    // Bit 4 is selected when bits 7:5 are clear.
    check_pos_from_bit4: assert property (
        @(posedge sel) ((in[7:5] == 3'b000) && in[4]) |-> (pos == 3'd4)
    );

    // Bit 3 is selected when bits 7:4 are clear.
    check_pos_from_bit3: assert property (
        @(posedge sel) ((in[7:4] == 4'b0000) && in[3]) |-> (pos == 3'd3)
    );

    // Bit 2 is selected when bits 7:3 are clear.
    check_pos_from_bit2: assert property (
        @(posedge sel) ((in[7:3] == 5'b00000) && in[2]) |-> (pos == 3'd2)
    );

    // Bit 1 is selected when bits 7:2 are clear.
    check_pos_from_bit1: assert property (
        @(posedge sel) ((in[7:2] == 6'b000000) && in[1]) |-> (pos == 3'd1)
    );

    // Bit 0 is selected when bits 7:1 are clear.
    check_pos_from_bit0: assert property (
        @(posedge sel) ((in[7:1] == 7'b0000000) && in[0]) |-> (pos == 3'd0)
    );

    // No asserted input bits produce position 0.
    check_pos_when_no_bits_set: assert property (
        @(posedge sel) (in == 8'b00000000) |-> (pos == 3'd0)
    );

    // The registered output is zero-extended from a 3-bit value.
    check_out_always_zero_extended: assert property (
        @(posedge sel) 1'b1 |=> (out_always[7:3] == 5'b00000)
    );

endmodule