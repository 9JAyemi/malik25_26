module counterB_sva (
    input logic [3:0] cntB_reg,
    input logic decrementB,
    input logic dual_countB,
    input logic cntB_en,
    input logic clk,
    input logic rst
);
    // Synchronous reset drives cntB_reg to zero.
    reset_clears_cntB: assert property (
        @(posedge clk) rst |-> (cntB_reg == 4'b0000)
    );

    // When disabled, cntB_reg holds its previous value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) (!cntB_en) |-> (cntB_reg == $past(cntB_reg))
    );

    // Any state change requires enable to be high.
    update_requires_enable: assert property (
        @(posedge clk) disable iff (rst) (cntB_reg != $past(cntB_reg)) |-> cntB_en
    );

    // Enabled up-count single-step: +1 modulo 16.
    inc_by1_when_enabled_up_single: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && !decrementB && !dual_countB) |-> (cntB_reg == ($past(cntB_reg) + 4'd1))
    );

    // Enabled up-count dual-step: +2 modulo 16.
    inc_by2_when_enabled_up_dual: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && !decrementB && dual_countB) |-> (cntB_reg == ($past(cntB_reg) + 4'd2))
    );

    // Enabled down-count single-step: -1 modulo 16.
    dec_by1_when_enabled_down_single: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && decrementB && !dual_countB) |-> (cntB_reg == ($past(cntB_reg) - 4'd1))
    );

    // Enabled down-count dual-step: -2 modulo 16.
    dec_by2_when_enabled_down_dual: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && decrementB && dual_countB) |-> (cntB_reg == ($past(cntB_reg) - 4'd2))
    );

    // Wrap: up-count single-step from 0xF goes to 0x0.
    wrap_up_single_from_F: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && !decrementB && !dual_countB && ($past(cntB_reg) == 4'hF)) |-> (cntB_reg == 4'h0)
    );

    // Wrap: up-count dual-step from 0xE goes to 0x0.
    wrap_up_dual_from_E: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && !decrementB && dual_countB && ($past(cntB_reg) == 4'hE)) |-> (cntB_reg == 4'h0)
    );

    // Wrap: down-count single-step from 0x0 goes to 0xF.
    wrap_down_single_from_0: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && decrementB && !dual_countB && ($past(cntB_reg) == 4'h0)) |-> (cntB_reg == 4'hF)
    );

    // Wrap: down-count dual-step from 0x0 goes to 0xE.
    wrap_down_dual_from_0: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && decrementB && dual_countB && ($past(cntB_reg) == 4'h0)) |-> (cntB_reg == 4'hE)
    );

    // Wrap: down-count dual-step from 0x1 goes to 0xF.
    wrap_down_dual_from_1: assert property (
        @(posedge clk) disable iff (rst)
            (cntB_en && decrementB && dual_countB && ($past(cntB_reg) == 4'h1)) |-> (cntB_reg == 4'hF)
    );
endmodule