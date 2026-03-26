module output_module_sva(
    input logic clk,
    input logic ctrl1_zone,
    input logic ctrl2_zone,
    input logic statusb_zone,
    input logic [9:0] p1_in,
    input logic [9:0] p2_in,
    input logic nwp,
    input logic ncd2,
    input logic ncd1,
    input logic system_mode,
    input logic [7:0] m68k_data
);

    // Output matches the RTL priority mux.
    check_full_mux_behavior: assert property (
        @(posedge clk) disable iff (1'b0)
        m68k_data == (ctrl1_zone ? 8'b00000000 :
                      ctrl2_zone ? 8'b00000000 :
                      statusb_zone ? {system_mode, nwp, ncd2, ncd1, p2_in[9:8], p1_in[9:8]} :
                                     p1_in[7:0])
    );

    // ctrl1_zone forces the output to zero.
    check_ctrl1_zone_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        ctrl1_zone |-> (m68k_data == 8'b00000000)
    );

    // ctrl2_zone forces the output to zero when ctrl1_zone is low.
    check_ctrl2_zone_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (!ctrl1_zone && ctrl2_zone) |-> (m68k_data == 8'b00000000)
    );

    // statusb_zone selects the packed status byte when higher priorities are low.
    check_statusb_zone_encoding: assert property (
        @(posedge clk) disable iff (1'b0)
        (!ctrl1_zone && !ctrl2_zone && statusb_zone) |->
            (m68k_data == {system_mode, nwp, ncd2, ncd1, p2_in[9:8], p1_in[9:8]})
    );

    // With no zone selected, p1_in[7:0] passes through.
    check_default_p1_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (!ctrl1_zone && !ctrl2_zone && !statusb_zone) |-> (m68k_data == p1_in[7:0])
    );

endmodule