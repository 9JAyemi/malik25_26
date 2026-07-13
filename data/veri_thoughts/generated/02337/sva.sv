module flipflop_adder_sva (
    input logic clk,
    input logic [7:0] reset,   // active-HIGH, synchronous per bit
    input logic [7:0] d,
    input logic [7:0] q,
    input logic [7:0] q_reg,   // internal
    input logic [7:0] sum      // internal
);
    // Output q mirrors internal sum.
    check_q_mirrors_sum: assert property (
        @(negedge clk) disable iff (|reset) q == sum
    );

    // sum[0] equals XOR of q_reg bits (1-bit additions truncate carries).
    check_sum_lsb_is_parity: assert property (
        @(negedge clk) disable iff (|reset) (sum[0] == ^q_reg)
    );

    // Upper bits of sum are always zero due to 1-bit addition width.
    check_sum_upper_zero: assert property (
        @(negedge clk) disable iff (|reset) (sum[7:1] == 7'd0)
    );

    // Upper bits of q are zero since q == sum.
    check_q_upper_zero: assert property (
        @(negedge clk) disable iff (|reset) (q[7:1] == 7'd0)
    );

    // q is always 0 or 1.
    check_q_range_is_0_or_1: assert property (
        @(negedge clk) disable iff (|reset) (q <= 8'd1)
    );

    // On each negedge, q_reg updates to previous (d & ~reset).
    check_qreg_updates_from_prev_d_masked: assert property (
        @(negedge clk) (q_reg == $past(d & ~reset))
    );

    // Next-cycle q LSB equals parity of previous d masked by ~reset.
    check_next_q_lsb_matches_prev_masked_d: assert property (
        @(negedge clk) (q[0] == ^($past(d & ~reset)))
    );

    // If all resets high, next-cycle q is zero.
    check_all_resets_clear_q: assert property (
        @(negedge clk) (&reset) |=> (q == 8'd0)
    );

    // If a given reset bit is high, that q_reg bit is 0 on the next negedge.
    genvar i_rst;
    generate
        for (i_rst = 0; i_rst < 8; i_rst++) begin : gen_reset_clear
            check_reset_high_clears_qreg: assert property (
                @(negedge clk) reset[i_rst] |=> (q_reg[i_rst] == 1'b0)
            );
        end
    endgenerate

    // When reset[i] is low, q_reg[i] captures d[i] by next negedge.
    genvar i_cap;
    generate
        for (i_cap = 0; i_cap < 8; i_cap++) begin : gen_capture
            check_capture_d_when_reset_low: assert property (
                @(negedge clk) (!reset[i_cap]) |=> (q_reg[i_cap] == $past(d[i_cap]))
            );
        end
    endgenerate
endmodule