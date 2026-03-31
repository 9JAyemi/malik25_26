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
    // o_dataout is the mux of i_register_settings and i_datain selected by i_settings.
    check_dataout_mux_function: assert property (
        @(posedge clock) disable iff (!resetn)
            o_dataout == (i_settings ? i_register_settings : i_datain)
    );

    // When i_settings is 1, o_dataout equals i_register_settings.
    check_dataout_sel_register_settings: assert property (
        @(posedge clock) disable iff (!resetn)
            i_settings |-> (o_dataout == i_register_settings)
    );

    // When i_settings is 0, o_dataout equals i_datain.
    check_dataout_sel_datain: assert property (
        @(posedge clock) disable iff (!resetn)
            !i_settings |-> (o_dataout == i_datain)
    );

    // o_dataout_valid passes through from i_datain_valid.
    check_valid_passthrough: assert property (
        @(posedge clock) disable iff (!resetn)
            o_dataout_valid == i_datain_valid
    );

    // o_datain_stall passes through from i_dataout_stall.
    check_stall_passthrough: assert property (
        @(posedge clock) disable iff (!resetn)
            o_datain_stall == i_dataout_stall
    );

    // If i_settings and both data inputs are stable, o_dataout remains stable.
    check_dataout_stable_when_all_inputs_stable: assert property (
        @(posedge clock) disable iff (!resetn)
            $stable(i_settings) && $stable(i_register_settings) && $stable(i_datain)
            |-> $stable(o_dataout)
    );

    // If i_datain_valid is stable, o_dataout_valid remains stable.
    check_valid_stable_when_input_valid_stable: assert property (
        @(posedge clock) disable iff (!resetn)
            $stable(i_datain_valid) |-> $stable(o_dataout_valid)
    );

    // If i_dataout_stall is stable, o_datain_stall remains stable.
    check_stall_stable_when_input_stall_stable: assert property (
        @(posedge clock) disable iff (!resetn)
            $stable(i_dataout_stall) |-> $stable(o_datain_stall)
    );

    // Changes on unselected i_datain do not affect o_dataout when selecting i_register_settings.
    check_independence_unselected_datain: assert property (
        @(posedge clock) disable iff (!resetn)
            i_settings && $stable(i_register_settings) && $changed(i_datain)
            |-> $stable(o_dataout)
    );

    // Changes on unselected i_register_settings do not affect o_dataout when selecting i_datain.
    check_independence_unselected_regsettings: assert property (
        @(posedge clock) disable iff (!resetn)
            !i_settings && $stable(i_datain) && $changed(i_register_settings)
            |-> $stable(o_dataout)
    );
endmodule