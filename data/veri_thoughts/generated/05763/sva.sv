module adbg_crc32_sva (
    input logic        clk,
    input logic        data,
    input logic        enable,
    input logic        shift,
    input logic        clr,
    input logic        rst,
    input logic [31:0] crc_out,
    input logic        serial_out
);

    function automatic [31:0] next_crc (
        input logic [31:0] crc_prev,
        input logic        data_prev
    );
        begin
            next_crc[0]  = crc_prev[1];
            next_crc[1]  = crc_prev[2];
            next_crc[2]  = crc_prev[3];
            next_crc[3]  = crc_prev[4];
            next_crc[4]  = crc_prev[5];
            next_crc[5]  = crc_prev[6]  ^ data_prev ^ crc_prev[0];
            next_crc[6]  = crc_prev[7];
            next_crc[7]  = crc_prev[8];
            next_crc[8]  = crc_prev[9]  ^ data_prev ^ crc_prev[0];
            next_crc[9]  = crc_prev[10] ^ data_prev ^ crc_prev[0];
            next_crc[10] = crc_prev[11];
            next_crc[11] = crc_prev[12];
            next_crc[12] = crc_prev[13];
            next_crc[13] = crc_prev[14];
            next_crc[14] = crc_prev[15];
            next_crc[15] = crc_prev[16] ^ data_prev ^ crc_prev[0];
            next_crc[16] = crc_prev[17];
            next_crc[17] = crc_prev[18];
            next_crc[18] = crc_prev[19];
            next_crc[19] = crc_prev[20] ^ data_prev ^ crc_prev[0];
            next_crc[20] = crc_prev[21] ^ data_prev ^ crc_prev[0];
            next_crc[21] = crc_prev[22] ^ data_prev ^ crc_prev[0];
            next_crc[22] = crc_prev[23];
            next_crc[23] = crc_prev[24] ^ data_prev ^ crc_prev[0];
            next_crc[24] = crc_prev[25] ^ data_prev ^ crc_prev[0];
            next_crc[25] = crc_prev[26];
            next_crc[26] = crc_prev[27] ^ data_prev ^ crc_prev[0];
            next_crc[27] = crc_prev[28] ^ data_prev ^ crc_prev[0];
            next_crc[28] = crc_prev[29];
            next_crc[29] = crc_prev[30] ^ data_prev ^ crc_prev[0];
            next_crc[30] = crc_prev[31] ^ data_prev ^ crc_prev[0];
            next_crc[31] =              data_prev ^ crc_prev[0];
        end
    endfunction

    // Reset drives the CRC state to all ones.
    check_reset_value: assert property (
        @(posedge clk) rst |=> (crc_out == 32'hffffffff && serial_out == 1'b1)
    );

    // serial_out always mirrors the CRC LSB.
    check_serial_matches_lsb: assert property (
        @(posedge clk) disable iff (rst) (serial_out == crc_out[0])
    );

    // clr loads all ones and has priority over enable and shift.
    check_clear_sets_all_ones: assert property (
        @(posedge clk) disable iff (rst)
        clr |=> (crc_out == 32'hffffffff && serial_out == 1'b1)
    );

    // enable updates the CRC with the implemented feedback polynomial.
    check_enable_updates_crc: assert property (
        @(posedge clk) disable iff (rst)
        (enable && !clr) |=> (crc_out == next_crc($past(crc_out), $past(data)))
    );

    // shift right occurs only when enable and clr are not active.
    check_shift_right: assert property (
        @(posedge clk) disable iff (rst)
        (shift && !enable && !clr) |=> (crc_out == {1'b0, $past(crc_out[31:1])})
    );

    // With no control active, the CRC register holds its value.
    check_idle_holds_crc: assert property (
        @(posedge clk) disable iff (rst)
        (!clr && !enable && !shift) |=> (crc_out == $past(crc_out))
    );

endmodule