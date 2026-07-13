module wb_mux_sva #(
    parameter int width = 32
)(
    input  logic               clk,
    input  logic               rst,
    input  logic               wb_freeze,
    input  logic [2:0]         rfwb_op,
    input  logic [width-1:0]   muxin_a,
    input  logic [width-1:0]   muxin_b,
    input  logic [width-1:0]   muxin_c,
    input  logic [width-1:0]   muxin_d,
    input  logic [width-1:0]   muxout,
    input  logic [width-1:0]   muxreg,
    input  logic               muxreg_valid
);

    ///// Reset behavior /////
    // During reset, muxreg and muxreg_valid are driven to zero.
    reset_drives_regs_zero: assert property (
        @(posedge clk) rst |-> (muxreg == '0) && (muxreg_valid == 1'b0)
    );

    ///// Freeze behavior /////
    // When wb_freeze is HIGH, muxreg holds its previous value.
    freeze_holds_muxreg: assert property (
        @(posedge clk) disable iff (rst) (wb_freeze && $past(!rst)) |=> (muxreg == $past(muxreg))
    );
    // When wb_freeze is HIGH, muxreg_valid holds its previous value.
    freeze_holds_muxreg_valid: assert property (
        @(posedge clk) disable iff (rst) (wb_freeze && $past(!rst)) |=> (muxreg_valid == $past(muxreg_valid))
    );

    ///// Sequential capture when not frozen /////
    // When not frozen, muxreg captures muxout on the next clock.
    capture_muxout_when_not_frozen: assert property (
        @(posedge clk) disable iff (rst) (!wb_freeze && $past(!rst)) |=> (muxreg == $past(muxout))
    );
    // When not frozen, muxreg_valid captures rfwb_op[0] on the next clock.
    capture_valid_when_not_frozen: assert property (
        @(posedge clk) disable iff (rst) (!wb_freeze && $past(!rst)) |=> (muxreg_valid == $past(rfwb_op[0]))
    );

    ///// Combinational muxout selection /////
    // rfwb_op[2:1]==00 selects muxin_a.
    muxout_select_a: assert property (
        @(posedge clk) disable iff (rst) (rfwb_op[2:1] == 2'b00) |-> (muxout == muxin_a)
    );
    // rfwb_op[2:1]==01 selects muxin_b.
    muxout_select_b: assert property (
        @(posedge clk) disable iff (rst) (rfwb_op[2:1] == 2'b01) |-> (muxout == muxin_b)
    );
    // rfwb_op[2:1]==10 selects muxin_c.
    muxout_select_c: assert property (
        @(posedge clk) disable iff (rst) (rfwb_op[2:1] == 2'b10) |-> (muxout == muxin_c)
    );
    // rfwb_op[2:1]==11 selects muxin_d + 8.
    muxout_select_d_plus8: assert property (
        @(posedge clk) disable iff (rst) (rfwb_op[2:1] == 2'b11) |-> (muxout == (muxin_d + 32'h8))
    );

    ///// End-to-end capture for d+8 path /////
    // When not frozen and selecting d+8, muxreg captures muxin_d+8 on the next clock.
    capture_d_plus8_on_unfreeze: assert property (
        @(posedge clk) disable iff (rst) (!wb_freeze && (rfwb_op[2:1] == 2'b11) && $past(!rst)) |=> (muxreg == $past(muxin_d + 32'h8))
    );

endmodule