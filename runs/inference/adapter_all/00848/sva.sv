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
    check_output_mux: assert property (
        @(posedge clock) disable iff (!resetn)
        o_dataout == (i_settings ? i_register_settings : i_datain)
    );

    // o_dataout_valid mirrors i_datain_valid.
    check_output_valid_passthrough: assert property (
        @(posedge clock) disable iff (!resetn)
        o_dataout_valid == i_datain_valid
    );

    // o_datain_stall mirrors i_dataout_stall.
    check_input_stall_passthrough: assert property (
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

    // A valid output requires a valid input.
    check_valid_output_requires_valid_input: assert property (
        @(posedge clock) disable iff (!resetn)
        o_dataout_valid |-> i_datain_valid
    );

    // A valid input must drive a valid output.
    check_valid_input_requires_valid_output: assert property (
        @(posedge clock) disable iff (!resetn)
        i_datain_valid |-> o_dataout_valid
    );

    // A stall on the output must come from the input stall.
    check_output_stall_matches_input_stall: assert property (
        @(posedge clock) disable iff (!resetn)
        o_datain_stall |-> i_dataout_stall
    );

    // A stall on the input must appear on the output stall.
    check_input_stall_matches_output_stall: assert property (
        @(posedge clock) disable iff (!resetn)
        i_dataout_stall |-> o_datain_stall
    );

endmodule