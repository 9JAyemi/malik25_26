module DecodeUnitRegisterTwo_sva (
    input logic       CLK,
    input logic       input_IN,
    input logic       wren_IN,
    input logic [2:0] writeAd_IN,
    input logic       ADR_MUX_IN,
    input logic       write_IN,
    input logic       PC_load_IN,
    input logic       SPR_w_IN,
    input logic       SPR_i_IN,
    input logic       SPR_d_IN,
    input logic [2:0] cond_IN,
    input logic [2:0] op2_IN,
    input logic       SW_IN,
    input logic       MAD_MUX_IN,
    input logic       input_OUT,
    input logic       wren_OUT,
    input logic [2:0] writeAd_OUT,
    input logic       ADR_MUX_OUT,
    input logic       write_OUT,
    input logic       PC_load_OUT,
    input logic       SPR_w_OUT,
    input logic       SPR_i_OUT,
    input logic       SPR_d_OUT,
    input logic [2:0] cond_OUT,
    input logic [2:0] op2_OUT,
    input logic       SW_OUT,
    input logic       MAD_MUX_OUT
);

    // input_OUT is the prior-cycle input_IN value.
    check_input_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (input_OUT == $past(input_IN))
    );

    // wren_OUT is the prior-cycle wren_IN value.
    check_wren_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (wren_OUT == $past(wren_IN))
    );

    // writeAd_OUT is the prior-cycle writeAd_IN value.
    check_writead_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (writeAd_OUT == $past(writeAd_IN))
    );

    // ADR_MUX_OUT is the prior-cycle ADR_MUX_IN value.
    check_adr_mux_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (ADR_MUX_OUT == $past(ADR_MUX_IN))
    );

    // write_OUT is the prior-cycle write_IN value.
    check_write_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (write_OUT == $past(write_IN))
    );

    // PC_load_OUT is the prior-cycle PC_load_IN value.
    check_pc_load_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (PC_load_OUT == $past(PC_load_IN))
    );

    // SPR_w_OUT is the prior-cycle SPR_w_IN value.
    check_spr_w_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (SPR_w_OUT == $past(SPR_w_IN))
    );

    // SPR_i_OUT is the prior-cycle SPR_i_IN value.
    check_spr_i_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (SPR_i_OUT == $past(SPR_i_IN))
    );

    // SPR_d_OUT is the prior-cycle SPR_d_IN value.
    check_spr_d_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (SPR_d_OUT == $past(SPR_d_IN))
    );

    // cond_OUT is the prior-cycle cond_IN value.
    check_cond_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (cond_OUT == $past(cond_IN))
    );

    // op2_OUT is the prior-cycle op2_IN value.
    check_op2_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (op2_OUT == $past(op2_IN))
    );

    // SW_OUT is the prior-cycle SW_IN value.
    check_sw_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (SW_OUT == $past(SW_IN))
    );

    // MAD_MUX_OUT is the prior-cycle MAD_MUX_IN value.
    check_mad_mux_out_registered: assert property (
        @(posedge CLK) 1'b1 |=> (MAD_MUX_OUT == $past(MAD_MUX_IN))
    );

endmodule