module excess_3_converter_sva (
    input logic [3:0] binary,
    input logic [7:0] excess_3
);
    // Output equals zero-extended (binary + 3) on any binary change.
    check_excess3_concat: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (excess_3 == {4'b0000, binary + 4'b0011})
    );

    // Upper nibble is always zero on any binary change.
    check_upper_nibble_zero: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (excess_3[7:4] == 4'b0000)
    );

    // Lower nibble equals binary + 3 (mod 16) on any binary change.
    check_lower_nibble_sum: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (excess_3[3:0] == (binary + 4'b0011))
    );

    // For binary == 0, output is 0x03.
    check_map_0_to_3: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (binary == 4'h0) |-> (excess_3 == 8'h03)
    );

    // For binary == 13 (0xD), output is 0x00 due to 4-bit wrap.
    check_map_d_to_0: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (binary == 4'hd) |-> (excess_3 == 8'h00)
    );

    // For binary == 14 (0xE), output is 0x01 due to 4-bit wrap.
    check_map_e_to_1: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (binary == 4'he) |-> (excess_3 == 8'h01)
    );

    // For binary == 15 (0xF), output is 0x02 due to 4-bit wrap.
    check_map_f_to_2: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (binary == 4'hf) |-> (excess_3 == 8'h02)
    );
endmodule