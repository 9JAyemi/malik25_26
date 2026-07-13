module shift_register_ring_counter_sva (
    input logic       clk,
    input logic       d,
    input logic       q,
    input logic [2:0] shift_reg
);

    // q always reflects the MSB of the shift register.
    check_q_tracks_shift_reg_msb: assert property (
        @(posedge clk) q == shift_reg[2]
    );

    // The shift register shifts left and appends d on each clock.
    check_shift_reg_update: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg == {$past(shift_reg[1:0]), $past(d)})
    );

    // Bit 0 captures d from the previous clock edge.
    check_stage0_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg[0] == $past(d))
    );

    // Bit 1 captures the previous value of bit 0.
    check_stage1_shifts_stage0: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg[1] == $past(shift_reg[0]))
    );

    // Bit 2 captures the previous value of bit 1.
    check_stage2_shifts_stage1: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg[2] == $past(shift_reg[1]))
    );

    // q matches d from three sampled clock edges earlier.
    check_q_matches_delayed_d: assert property (
        @(posedge clk) 1'b1 |=> ##2 (q == $past(d,3))
    );

endmodule