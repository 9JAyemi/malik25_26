module Johnson_counter_sva (
    input logic        clk,
    input logic        rst_n,       // active-low reset
    input logic [7:0]  Q,
    input logic [7:0]  shift_reg
);

    ///// Reset behavior /////
    // During reset, shift_reg and Q clear to 0.
    check_reset_clears_regs: assert property (
        @(posedge clk) (!rst_n) |-> (shift_reg == 8'h00) && (Q == 8'h00)
    );

    // On reset deassertion, first-cycle shift_reg and Q are 0.
    check_post_reset_values: assert property (
        @(posedge clk) $rose(rst_n) |-> (shift_reg == 8'h00) && (Q == 8'h00)
    );

    ///// State update /////
    // When running, shift_reg rotates left by one bit each cycle.
    check_shift_rotate_left: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) |-> (shift_reg == { $past(shift_reg)[6:0], $past(shift_reg)[7] })
    );

    ///// Q decode from previous shift_reg /////
    // Q=0x00 when previous shift_reg is 0x00 or 0xFF.
    map_q_from_sr_0000: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) && (($past(shift_reg) == 8'h00) || ($past(shift_reg) == 8'hFF))
            |-> (Q == 8'h00)
    );

    // Q=0x01 when previous shift_reg is 0x80 or 0x7F.
    map_q_from_sr_0001: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) && (($past(shift_reg) == 8'h80) || ($past(shift_reg) == 8'h7F))
            |-> (Q == 8'h01)
    );

    // Q=0x03 when previous shift_reg is 0xC0 or 0x3F.
    map_q_from_sr_0011: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) && (($past(shift_reg) == 8'hC0) || ($past(shift_reg) == 8'h3F))
            |-> (Q == 8'h03)
    );

    // Q=0x07 when previous shift_reg is 0xE0 or 0x1F.
    map_q_from_sr_0111: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) && (($past(shift_reg) == 8'hE0) || ($past(shift_reg) == 8'h1F))
            |-> (Q == 8'h07)
    );

    // Q=0x0F when previous shift_reg is 0xF0 or 0x0F.
    map_q_from_sr_1111: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) && (($past(shift_reg) == 8'hF0) || ($past(shift_reg) == 8'h0F))
            |-> (Q == 8'h0F)
    );

    // Q=0x0E when previous shift_reg is 0xF8 or 0x07.
    map_q_from_sr_1110: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) && (($past(shift_reg) == 8'hF8) || ($past(shift_reg) == 8'h07))
            |-> (Q == 8'h0E)
    );

    // Q=0x0C when previous shift_reg is 0xFC or 0x03.
    map_q_from_sr_1100: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) && (($past(shift_reg) == 8'hFC) || ($past(shift_reg) == 8'h03))
            |-> (Q == 8'h0C)
    );

    // Q=0x08 when previous shift_reg is 0xFE or 0x01.
    map_q_from_sr_1000: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) && (($past(shift_reg) == 8'hFE) || ($past(shift_reg) == 8'h01))
            |-> (Q == 8'h08)
    );

    // If previous shift_reg not in decode table, Q holds its value.
    check_q_holds_on_no_match: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) &&
            !($past(shift_reg) inside {8'h00,8'h80,8'hC0,8'hE0,8'hF0,8'hF8,8'hFC,8'hFE,
                                       8'hFF,8'h7F,8'h3F,8'h1F,8'h0F,8'h07,8'h03,8'h01})
            |-> (Q == $past(Q))
    );

    ///// Q value invariants /////
    // Upper nibble of Q is always zero (due to 4-bit assignments).
    check_q_upper_nibble_zero: assert property (
        @(posedge clk) (Q[7:4] == 4'b0000)
    );

    // Q[3:0] is always one of the defined decode values.
    check_q_lsb_allowed_set: assert property (
        @(posedge clk) disable iff (!rst_n)
            (Q[3:0] inside {4'h0,4'h1,4'h3,4'h7,4'hF,4'hE,4'hC,4'h8})
    );

endmodule