module decoder_priority_encoder_sva (
    input  logic        clk,          // sampling clock for assertions
    input  logic [1:0]  sel,
    input  logic        enable,
    input  logic [15:0] out,
    input  logic [1:0]  priority_sel  // internal DUT signal
);
    ///// Priority select behavior /////
    // When enabled, priority_sel mirrors sel.
    check_priority_sel_when_enabled: assert property (
        @(posedge clk) (enable == 1'b1) |-> (priority_sel == sel)
    );

    // When disabled, priority_sel is forced to 2'b00.
    check_priority_sel_when_disabled: assert property (
        @(posedge clk) (enable == 1'b0) |-> (priority_sel == 2'b00)
    );

    ///// Output mapping from priority_sel /////
    // priority_sel 00 maps to out = 0x0001.
    check_out_map_ps00: assert property (
        @(posedge clk) (priority_sel == 2'b00) |-> (out == 16'h0001)
    );

    // priority_sel 01 maps to out = 0x0002.
    check_out_map_ps01: assert property (
        @(posedge clk) (priority_sel == 2'b01) |-> (out == 16'h0002)
    );

    // priority_sel 10 maps to out = 0x0004.
    check_out_map_ps10: assert property (
        @(posedge clk) (priority_sel == 2'b10) |-> (out == 16'h0004)
    );

    // priority_sel 11 maps to out = 0x0008.
    check_out_map_ps11: assert property (
        @(posedge clk) (priority_sel == 2'b11) |-> (out == 16'h0008)
    );

    ///// Structural properties of out /////
    // Upper 12 bits of out are always zero.
    check_out_upper_zero: assert property (
        @(posedge clk) (out[15:4] == 12'h000)
    );

    // Lower nibble of out is one-hot.
    check_out_lower_onehot: assert property (
        @(posedge clk) $onehot(out[3:0])
    );

    ///// Direct input-to-output mapping /////
    // When disabled, out is 0x0001.
    check_out_when_disabled: assert property (
        @(posedge clk) (enable == 1'b0) |-> (out == 16'h0001)
    );

    // When enabled, out equals 1 shifted by sel.
    check_out_when_enabled: assert property (
        @(posedge clk) (enable == 1'b1) |-> (out == (16'h0001 << sel))
    );

    // Out equals 1 shifted by priority_sel.
    check_out_matches_priority_sel: assert property (
        @(posedge clk) out == (16'h0001 << priority_sel)
    );
endmodule