module crc_sva (
    input logic [0:0] data_in,
    input logic crc_en,
    input logic [15:0] crc_out,
    input logic rst,
    input logic clk,
    // Internal signals from DUT for binding
    input logic [15:0] lfsr_q,
    input logic [15:0] lfsr_c
);
    ///// Reset behavior /////
    // When reset is asserted, internal state clears to zero.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |-> (lfsr_q == 16'h0000)
    );
    // When reset is asserted, output reflects cleared state.
    check_reset_drives_output_zero: assert property (
        @(posedge clk) rst |-> (crc_out == 16'h0000)
    );

    ///// Output mapping /////
    // Output always reflects internal state.
    check_output_equals_state: assert property (
        @(posedge clk) disable iff (rst) (crc_out == lfsr_q)
    );

    ///// Enable-controlled state update /////
    // When enable is LOW, state holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) (!crc_en) |=> (lfsr_q == $past(lfsr_q))
    );
    // When enable is HIGH, state updates to previous cycle's combinational next value.
    check_update_when_enabled: assert property (
        @(posedge clk) disable iff (rst) (crc_en) |=> (lfsr_q == $past(lfsr_c))
    );

    ///// Combinational next-state equations (lfsr_c) /////
    // Next-state bit 0 equals lfsr_q[15] XOR data_in[0].
    check_lfsr_c_bit0_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[0] == (lfsr_q[15] ^ data_in[0]))
    );
    // Next-state bit 1 equals lfsr_q[0].
    check_lfsr_c_bit1_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[1] == lfsr_q[0])
    );
    // Next-state bit 2 equals lfsr_q[1] XOR lfsr_q[15] XOR data_in[0].
    check_lfsr_c_bit2_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[2] == (lfsr_q[1] ^ lfsr_q[15] ^ data_in[0]))
    );
    // Next-state bit 3 equals lfsr_q[2].
    check_lfsr_c_bit3_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[3] == lfsr_q[2])
    );
    // Next-state bit 4 equals lfsr_q[3].
    check_lfsr_c_bit4_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[4] == lfsr_q[3])
    );
    // Next-state bit 5 equals lfsr_q[4].
    check_lfsr_c_bit5_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[5] == lfsr_q[4])
    );
    // Next-state bit 6 equals lfsr_q[5].
    check_lfsr_c_bit6_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[6] == lfsr_q[5])
    );
    // Next-state bit 7 equals lfsr_q[6].
    check_lfsr_c_bit7_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[7] == lfsr_q[6])
    );
    // Next-state bit 8 equals lfsr_q[7].
    check_lfsr_c_bit8_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[8] == lfsr_q[7])
    );
    // Next-state bit 9 equals lfsr_q[8].
    check_lfsr_c_bit9_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[9] == lfsr_q[8])
    );
    // Next-state bit 10 equals lfsr_q[9].
    check_lfsr_c_bit10_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[10] == lfsr_q[9])
    );
    // Next-state bit 11 equals lfsr_q[10].
    check_lfsr_c_bit11_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[11] == lfsr_q[10])
    );
    // Next-state bit 12 equals lfsr_q[11].
    check_lfsr_c_bit12_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[12] == lfsr_q[11])
    );
    // Next-state bit 13 equals lfsr_q[12].
    check_lfsr_c_bit13_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[13] == lfsr_q[12])
    );
    // Next-state bit 14 equals lfsr_q[13].
    check_lfsr_c_bit14_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[14] == lfsr_q[13])
    );
    // Next-state bit 15 equals lfsr_q[14] XOR lfsr_q[15] XOR data_in[0].
    check_lfsr_c_bit15_def: assert property (
        @(posedge clk) disable iff (rst) (lfsr_c[15] == (lfsr_q[14] ^ lfsr_q[15] ^ data_in[0]))
    );

endmodule