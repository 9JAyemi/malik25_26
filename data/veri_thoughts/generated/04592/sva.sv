module program_counter_sva(
    input logic        clk,
    input logic        rst,
    input logic [5:0]  address,
    input logic [31:0] Inst_code
);

    // When sampled reset is high, the instruction output is zero.
    check_reset_inst_code_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |-> (Inst_code == 32'd0)
    );

    // When sampled reset is high, the address output is zero.
    check_reset_address_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |-> (address == 6'd0)
    );

    // Address always reflects instruction bits [7:2].
    check_address_tracks_inst_code: assert property (
        @(posedge clk) disable iff (rst)
        address == Inst_code[7:2]
    );

    // After a sampled reset cycle, the next sampled instruction is still zero.
    check_post_reset_inst_code_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (Inst_code == 32'd0)
    );

    // After a sampled reset cycle, the next sampled address is still zero.
    check_post_reset_address_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (address == 6'd0)
    );

    // Between sampled cycles, Inst_code either increments by 4 or has been reset to zero.
    check_inst_code_steps_by_four_or_resets: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (Inst_code == ($past(Inst_code) + 32'd4)) || (Inst_code == 32'd0)
    );

    // Between sampled cycles, address either increments by 1 or has been reset to zero.
    check_address_steps_by_one_or_resets: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (address == ($past(address) + 6'd1)) || (address == 6'd0)
    );

    // Adding 4 preserves Inst_code[1:0] unless reset drives them to zero.
    check_inst_code_low_bits_hold_or_reset: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (Inst_code[1:0] == $past(Inst_code[1:0])) || (Inst_code[1:0] == 2'b00)
    );

endmodule