module vfabric_bypass_reg_sva (
    input logic clock,
    input logic resetn,
    input logic i_settings,
    input logic [31:0] i_register_settings,
    input logic [31:0] i_datain,
    input logic i_datain_valid,
    output logic o_datain_stall,
    output logic [31:0] o_dataout,
    output logic o_dataout_valid,
    input logic i_dataout_stall
);
    // Sequential logic: o_dataout and o_dataout_valid are driven by the clock
    // Combinational logic: o_dataout and o_dataout_valid are driven by i_settings, i_register_settings, and i_datain

    // o_dataout should be equal to i_register_settings when i_settings is high
    bypass_reg_1: assert property (
        @(posedge clock) disable iff (!resetn) (i_settings == 1'b1) |-> (o_dataout == i_register_settings)
    );

    // o_dataout should be equal to i_datain when i_settings is low
    bypass_reg_2: assert property (
        @(posedge clock) disable iff (!resetn) (i_settings == 1'b0) |-> (o_dataout == i_datain)
    );

    // o_dataout_valid should be equal to i_datain_valid
    bypass_reg_3: assert property (
        @(posedge clock) disable iff (!resetn) (o_dataout_valid == i_datain_valid)
    );

    // o_datain_stall should be equal to i_dataout_stall
    bypass_reg_4: assert property (
        @(posedge clock) disable iff (!resetn) (o_datain_stall == i_dataout_stall)
    );

    // At reset, o_dataout and o_dataout_valid should be low
    reset_1: assert property (
        @(posedge clock) !resetn |-> (o_dataout == 32'b0) && (o_dataout_valid == 1'b0)
    );

    // At reset, o_datain_stall should be low
    reset_2: assert property (
        @(posedge clock) !resetn |-> (o_datain_stall == 1'b0)
    );

    // i_datain_valid should not be high when i_dataout_stall is high
    bypass_reg_5: assert property (
        @(posedge clock) disable iff (!resetn) (i_dataout_stall == 1'b1) |-> (i_datain_valid == 1'b0)
    );

    // i_settings should not be high when i_dataout_stall is high
    bypass_reg_6: assert property (
        @(posedge clock) disable iff (!resetn) (i_dataout_stall == 1'b1) |-> (i_settings == 1'b0)
    );

    // i_register_settings should not be used when i_dataout_stall is high
    bypass_reg_7: assert property (
        @(posedge clock) disable iff (!resetn) (i_dataout_stall == 1'b1) |-> (i_register_settings == 32'b0)
    );

    // i_datain should not be used when i_dataout_stall is high
    bypass_reg_8: assert property (
        @(posedge clock) disable iff (!resetn) (i_dataout_stall == 1'b1) |-> (i_datain == 32'b0)
    );

    // i_datain_valid should not be high when o_datain_stall is high
    bypass_reg_9: assert property (
        @(posedge clock) disable iff (!resetn) (o_datain_stall == 1'b1) |-> (i_datain_valid == 1'b0)
    );

    // i_settings should not be high when o_datain_stall is high
    bypass_reg_10: assert property (
        @(posedge clock) disable iff (!resetn) (o_datain_stall == 1'b1) |-> (i_settings == 1'b0)
    );
endmodule