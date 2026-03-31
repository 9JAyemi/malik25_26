module vfabric_bypass_reg_sva #(
    parameter DATA_WIDTH = 32
) (
    input logic clock,
    input logic resetn,
    input logic i_settings,
    input logic [DATA_WIDTH-1:0] i_register_settings,
    input logic [DATA_WIDTH-1:0] i_datain,
    input logic i_datain_valid,
    input logic o_datain_stall,
    input logic [DATA_WIDTH-1:0] o_dataout,
    input logic o_dataout_valid,
    input logic i_dataout_stall
);

    // o_dataout follows the mux select between i_register_settings and i_datain.
    check_output_mux_function: assert property (
        @(posedge clock) disable iff (!resetn)
        o_dataout == (i_settings ? i_register_settings : i_datain)
    );

    // o_dataout_valid is a direct pass-through of i_datain_valid.
    check_valid_passthrough: assert property (
        @(posedge clock) disable iff (!resetn)
        o_dataout_valid == i_datain_valid
    );

    // o_datain_stall is a direct pass-through of i_dataout_stall.
    check_stall_passthrough: assert property (
        @(posedge clock) disable iff (!resetn)
        o_datain_stall == i_dataout_stall
    );

    // When i_settings is high, o_dataout selects i_register_settings.
    check_select_register_settings: assert property (
        @(posedge clock) disable iff (!resetn)
        i_settings |-> (o_dataout == i_register_settings)
    );

    // When i_settings is low, o_dataout selects i_datain.
    check_select_datain: assert property (
        @(posedge clock) disable iff (!resetn)
        !i_settings |-> (o_dataout == i_datain)
    );

    // A high i_datain_valid is always reflected on o_dataout_valid.
    check_valid_high_when_datain_valid: assert property (
        @(posedge clock) disable iff (!resetn)
        i_datain_valid |-> o_dataout_valid
    );

    // A low i_datain_valid is always reflected on o_dataout_valid.
    check_valid_low_when_datain_invalid: assert property (
        @(posedge clock) disable iff (!resetn)
        !i_datain_valid |-> !o_dataout_valid
    );

    // A high i_dataout_stall is always reflected on o_datain_stall.
    check_stall_high_when_dataout_stall: assert property (
        @(posedge clock) disable iff (!resetn)
        i_dataout_stall |-> o_datain_stall
    );

    // A low i_dataout_stall is always reflected on o_datain_stall.
    check_stall_low_when_dataout_not_stall: assert property (
        @(posedge clock) disable iff (!resetn)
        !i_dataout_stall |-> !o_datain_stall
    );

endmodule