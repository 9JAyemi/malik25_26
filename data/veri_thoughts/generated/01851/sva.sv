module mux3to1_async_reset_ce_sva (
    input logic [2:0] data_in,
    input logic sel,
    input logic clk,
    input logic reset,     // active-low asynchronous reset
    input logic enable,
    input logic out,
    // Internal signals available in RTL (bind hierarchically when using this SVA)
    input logic [2:0] data_reg,
    input logic sel_inv
);

    ///// Reset behavior /////
    // While reset is asserted LOW, registers are held at zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) !reset |-> (data_reg == 3'b000) && (out == 1'b0)
    );
    // One cycle after observing reset LOW, values remain zero.
    check_reset_holds_zero_next: assert property (
        @(posedge clk) !reset |=> (data_reg == 3'b000) && (out == 1'b0)
    );

    ///// Gating with enable /////
    // With enable LOW, data_reg holds its value.
    check_data_reg_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!reset) !enable |=> $stable(data_reg)
    );
    // With enable LOW, out holds its value.
    check_out_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!reset) !enable |=> $stable(out)
    );

    ///// Load behavior /////
    // With enable HIGH, data_reg captures data_in.
    check_data_reg_load_on_enable: assert property (
        @(posedge clk) disable iff (!reset) enable |=> (data_reg == $past(data_in))
    );

    ///// Muxing behavior for out /////
    // With enable HIGH and sel==1, out captures previous data_reg[0].
    check_out_update_sel1: assert property (
        @(posedge clk) disable iff (!reset) (enable && sel) |=> (out == $past(data_reg[0]))
    );
    // With enable HIGH and sel==0, out captures previous data_reg[2].
    check_out_update_sel0: assert property (
        @(posedge clk) disable iff (!reset) (enable && !sel) |=> (out == $past(data_reg[2]))
    );

    ///// Combinational relations /////
    // sel_inv is always the bitwise inversion of sel.
    check_sel_inv_complement: assert property (
        @(posedge clk) disable iff (!reset) (sel_inv == ~sel)
    );

endmodule