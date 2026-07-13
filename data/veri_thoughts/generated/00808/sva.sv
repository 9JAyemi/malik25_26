module delay_gate_sva (
    input logic A,
    input logic reset,      // synchronous active-high reset
    input logic X,
    input logic clk,
    input logic [3:0] delay_reg
);
    // During reset, X and delay_reg are cleared on the next clock.
    check_reset_clears_next: assert property (
        @(posedge clk) reset |=> (delay_reg == 4'b0000) && (X == 1'b0)
    );

    // On non-reset cycles (looking back one cycle), delay_reg shifts A into LSB.
    check_shift_vector_update: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (delay_reg == { $past(delay_reg[2:0]), $past(A) })
    );

    // MSB gets previous bit[2] on non-reset cycles.
    check_bit3_shifts_from_bit2: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (delay_reg[3] == $past(delay_reg[2]))
    );

    // bit[2] gets previous bit[1] on non-reset cycles.
    check_bit2_shifts_from_bit1: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (delay_reg[2] == $past(delay_reg[1]))
    );

    // bit[1] gets previous bit[0] on non-reset cycles.
    check_bit1_shifts_from_bit0: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (delay_reg[1] == $past(delay_reg[0]))
    );

    // LSB gets previous A on non-reset cycles.
    check_lsb_captures_A: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (delay_reg[0] == $past(A))
    );

    // X gets previous delay_reg[3] on non-reset cycles.
    check_x_tracks_prev_msb: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (X == $past(delay_reg[3]))
    );

    // With 4 consecutive non-reset cycles, X equals A from 4 cycles ago.
    check_x_four_cycle_delay: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset,1) && $past(!reset,2) && $past(!reset,3) && $past(!reset,4))
            |-> (X == $past(A,4))
    );

    // After reset deasserts, X remains 0 for four cycles.
    check_x_zero_after_reset_fall: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (X == 1'b0)[*4]
    );

    // After reset deasserts, delay_reg[3] remains 0 for three cycles.
    check_msb_zero_three_after_reset_fall: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (delay_reg[3] == 1'b0)[*3]
    );
endmodule