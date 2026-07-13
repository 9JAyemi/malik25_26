module nonblocking_gate_sva (
    input logic        clk,
    input logic [4:0]  ctrl,
    input logic [1:0]  din,
    input logic [0:0]  sel,
    input logic [31:0] dout
);

    function automatic logic [31:0] rtl_next_dout(
        input logic [31:0] prev_dout,
        input logic [4:0]  prev_ctrl,
        input logic [1:0]  prev_din,
        input logic [0:0]  prev_sel
    );
        logic [31:0] tmp;
        begin
            tmp = prev_dout + 32'd1;
            case ((prev_ctrl * prev_sel) + 0)
                0:  tmp[31:0]  = prev_din;
                1:  tmp[31:1]  = prev_din;
                2:  tmp[31:2]  = prev_din;
                3:  tmp[31:3]  = prev_din;
                4:  tmp[31:4]  = prev_din;
                5:  tmp[31:5]  = prev_din;
                6:  tmp[31:6]  = prev_din;
                7:  tmp[31:7]  = prev_din;
                8:  tmp[31:8]  = prev_din;
                9:  tmp[31:9]  = prev_din;
                10: tmp[31:10] = prev_din;
                11: tmp[31:11] = prev_din;
                12: tmp[31:12] = prev_din;
                13: tmp[31:13] = prev_din;
                14: tmp[31:14] = prev_din;
                15: tmp[31:15] = prev_din;
                16: tmp[31:16] = prev_din;
                17: tmp[31:17] = prev_din;
                18: tmp[31:18] = prev_din;
                19: tmp[31:19] = prev_din;
                20: tmp[31:20] = prev_din;
                21: tmp[31:21] = prev_din;
                22: tmp[31:22] = prev_din;
                23: tmp[31:23] = prev_din;
                24: tmp[31:24] = prev_din;
                25: tmp[31:25] = prev_din;
                26: tmp[31:26] = prev_din;
                27: tmp[31:27] = prev_din;
                28: tmp[31:28] = prev_din;
                29: tmp[31:29] = prev_din;
                30: tmp[31:30] = prev_din;
                31: tmp[31:31] = prev_din;
                default: ;
            endcase
            rtl_next_dout = tmp;
        end
    endfunction

    function automatic logic [31:0] lower_mask(input logic [4:0] n);
        logic [5:0] shift_amt;
        begin
            if (n == 5'd0) begin
                lower_mask = 32'd0;
            end else begin
                shift_amt  = 6'd32 - {1'b0, n};
                lower_mask = 32'hFFFF_FFFF >> shift_amt;
            end
        end
    endfunction

    // dout matches the exact registered next-state behavior.
    check_dout_update_matches_rtl: assert property (
        @(posedge clk) disable iff ($initstate)
        dout == rtl_next_dout($past(dout), $past(ctrl), $past(din), $past(sel))
    );

    // sel low forces a full-register load from din.
    check_sel_low_loads_full_din: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(sel) == 1'b0) |-> (dout == {{30{1'b0}}, $past(din)})
    );

    // ctrl zero with sel high also forces a full-register load from din.
    check_ctrl_zero_loads_full_din: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(sel) == 1'b1 && $past(ctrl) == 5'd0) |-> (dout == {{30{1'b0}}, $past(din)})
    );

    // For shifted updates, the low ctrl bits come from the incremented old dout.
    check_shifted_update_preserves_low_bits: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(sel) == 1'b1 && $past(ctrl) != 5'd0) |->
        ((dout & lower_mask($past(ctrl))) == (($past(dout) + 32'd1) & lower_mask($past(ctrl))))
    );

    // For ctrl 1 through 30, din is inserted at bits ctrl+1:ctrl.
    check_shifted_update_inserts_din_bits: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(sel) == 1'b1 && $past(ctrl) >= 5'd1 && $past(ctrl) <= 5'd30) |->
        (((dout >> $past(ctrl)) & 32'd3) == $past(din))
    );

    // For ctrl 1 through 29, all bits above the inserted din bits are cleared.
    check_shifted_update_clears_upper_bits: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(sel) == 1'b1 && $past(ctrl) >= 5'd1 && $past(ctrl) <= 5'd29) |->
        ((dout >> ($past(ctrl) + 5'd2)) == 32'd0)
    );

    // At ctrl 31, only the top bit is overwritten and it takes din[0].
    check_ctrl31_uses_din_lsb_for_top_bit: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(sel) == 1'b1 && $past(ctrl) == 5'd31) |-> (dout[31] == $past(din[0]))
    );

endmodule