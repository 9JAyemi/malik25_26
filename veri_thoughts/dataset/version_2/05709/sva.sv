module test_LEDState_sva (
    input logic        rsi_MRST_reset,
    input logic        csi_MCLK_clk,

    input logic [23:0] aso_fled0_data,
    input logic        aso_fled0_valid,

    input logic [23:0] aso_fled1_data,
    input logic        aso_fled1_valid,

    input logic [23:0] aso_fled2_data,
    input logic        aso_fled2_valid,

    input logic [23:0] aso_fled3_data,
    input logic        aso_fled3_valid,

    input logic [5:0]  state,
    input logic [7:0]  r_cnt,
    input logic [7:0]  g_cnt,
    input logic [7:0]  b_cnt,
    input logic [18:0] delay_cnt
);

    // Reset drives the state, counters, and visible outputs to their default values.
    check_reset_defaults: assert property (
        @(posedge csi_MCLK_clk)
        rsi_MRST_reset |-> (state == 6'd0) &&
                           (r_cnt == 8'd0) &&
                           (g_cnt == 8'd0) &&
                           (b_cnt == 8'd0) &&
                           (delay_cnt == 19'd0) &&
                           (aso_fled0_valid == 1'b1) &&
                           (aso_fled1_valid == 1'b1) &&
                           (aso_fled2_valid == 1'b1) &&
                           (aso_fled3_valid == 1'b1) &&
                           (aso_fled0_data == 24'd0) &&
                           (aso_fled1_data == 24'd0) &&
                           (aso_fled2_data == 24'd0) &&
                           (aso_fled3_data == 24'd0)
    );

    // All valid signals are tied high.
    check_valid_always_high: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        (aso_fled0_valid == 1'b1) &&
        (aso_fled1_valid == 1'b1) &&
        (aso_fled2_valid == 1'b1) &&
        (aso_fled3_valid == 1'b1)
    );

    // Each output bus is the documented permutation of the RGB counters.
    check_output_data_mappings: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        (aso_fled0_data == {r_cnt, g_cnt, b_cnt}) &&
        (aso_fled1_data == {g_cnt, b_cnt, r_cnt}) &&
        (aso_fled2_data == {b_cnt, r_cnt, g_cnt}) &&
        (aso_fled3_data == {g_cnt, r_cnt, b_cnt})
    );

    // Ramp states increment the delay counter on non-terminal counts.
    check_ramp_delay_increments: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        (((state == 6'd0) || (state == 6'd2) || (state == 6'd4) ||
          (state == 6'd6) || (state == 6'd8) || (state == 6'd10)) &&
         (delay_cnt != 19'h7FFFF))
        |=> (delay_cnt == ($past(delay_cnt) + 19'd1))
    );

    // At the terminal delay count, the active color counter updates and delay wraps.
    check_terminal_delay_updates_active_color: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        (((state == 6'd0) || (state == 6'd2) || (state == 6'd4) ||
          (state == 6'd6) || (state == 6'd8) || (state == 6'd10)) &&
         (delay_cnt == 19'h7FFFF))
        |=> (delay_cnt == 19'd0) &&
            (
                (($past(state) == 6'd0)  && (r_cnt == ($past(r_cnt) + 8'h01)) && (g_cnt == 8'd0) && (b_cnt == 8'd0)) ||
                (($past(state) == 6'd2)  && (r_cnt == ($past(r_cnt) - 8'h01))) ||
                (($past(state) == 6'd4)  && (g_cnt == ($past(g_cnt) + 8'h01))) ||
                (($past(state) == 6'd6)  && (g_cnt == ($past(g_cnt) - 8'h01))) ||
                (($past(state) == 6'd8)  && (b_cnt == ($past(b_cnt) + 8'h01))) ||
                (($past(state) == 6'd10) && (b_cnt == ($past(b_cnt) - 8'h01)))
            )
    );

    // Full-scale counts move the rise phases into their transition states.
    check_full_scale_phase_transitions: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        (((state == 6'd0) && (r_cnt == 8'hFF)) ||
         ((state == 6'd4) && (g_cnt == 8'hFF)) ||
         ((state == 6'd8) && (b_cnt == 8'hFF)))
        |=> (
                (($past(state) == 6'd0) && (state == 6'd1)) ||
                (($past(state) == 6'd4) && (state == 6'd5)) ||
                (($past(state) == 6'd8) && (state == 6'd9))
            )
    );

    // States 1, 5, and 9 are single-cycle transitions that clear delay_cnt.
    check_transition_states_advance: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        ((state == 6'd1) || (state == 6'd5) || (state == 6'd9))
        |=> (delay_cnt == 19'd0) &&
            (
                (($past(state) == 6'd1) && (state == 6'd2)) ||
                (($past(state) == 6'd5) && (state == 6'd6)) ||
                (($past(state) == 6'd9) && (state == 6'd10))
            )
    );

    // Zero counts move the fall phases into their clear states.
    check_zero_scale_phase_transitions: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        (((state == 6'd2) && (r_cnt == 8'h00)) ||
         ((state == 6'd6) && (g_cnt == 8'h00)) ||
         ((state == 6'd10) && (b_cnt == 8'h00)))
        |=> (
                (($past(state) == 6'd2) && (state == 6'd3)) ||
                (($past(state) == 6'd6) && (state == 6'd7)) ||
                (($past(state) == 6'd10) && (state == 6'd11))
            )
    );

    // States 3, 7, and 11 clear all counters and advance to the next color phase.
    check_clear_states_advance: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        ((state == 6'd3) || (state == 6'd7) || (state == 6'd11))
        |=> (r_cnt == 8'd0) &&
            (g_cnt == 8'd0) &&
            (b_cnt == 8'd0) &&
            (delay_cnt == 19'd0) &&
            (
                (($past(state) == 6'd3) && (state == 6'd4)) ||
                (($past(state) == 6'd7) && (state == 6'd8)) ||
                (($past(state) == 6'd11) && (state == 6'd0))
            )
    );

    // Any out-of-range state follows the default branch back to state 0.
    check_illegal_state_recovers: assert property (
        @(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        (state > 6'd11)
        |=> (state == 6'd0) &&
            (r_cnt == 8'd0) &&
            (g_cnt == 8'd0) &&
            (b_cnt == 8'd0) &&
            (delay_cnt == 19'd0)
    );

endmodule

bind test_LEDState test_LEDState_sva u_test_LEDState_sva (.*);