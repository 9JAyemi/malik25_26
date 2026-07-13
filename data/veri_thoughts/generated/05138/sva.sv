module bw_io_cmos_edgelogic_sva (
    input logic clk,
    input logic data,
    input logic oe,
    input logic bsr_mode,
    input logic por_l,
    input logic bsr_data_to_core,
    input logic se,
    input logic rcvr_data,
    input logic pad_up,
    input logic pad_dn_l,
    input logic bsr_up,
    input logic bsr_dn_l,
    input logic por,
    input logic to_core
);

    // por is the inverse of por_l.
    check_por_inversion: assert property (
        @(posedge clk) disable iff (1'b0) (por == ~por_l)
    );

    // pad_up is asserted only when data and oe are both high.
    check_pad_up_function: assert property (
        @(posedge clk) disable iff (1'b0) (pad_up == (data && oe))
    );

    // pad_dn_l follows the implemented active-low drive equation.
    check_pad_dn_l_function: assert property (
        @(posedge clk) disable iff (1'b0) (pad_dn_l == ~(~data && oe))
    );

    // bsr_up mirrors pad_up.
    check_bsr_up_mirror: assert property (
        @(posedge clk) disable iff (1'b0) (bsr_up == pad_up)
    );

    // bsr_dn_l mirrors pad_dn_l.
    check_bsr_dn_l_mirror: assert property (
        @(posedge clk) disable iff (1'b0) (bsr_dn_l == pad_dn_l)
    );

    // to_core follows the mux implemented in the RTL.
    check_to_core_mux_function: assert property (
        @(posedge clk) disable iff (1'b0)
        (to_core == ((bsr_mode && !se) ? bsr_data_to_core : rcvr_data))
    );

    // In boundary-scan mode with se low, to_core selects bsr_data_to_core.
    check_to_core_bsr_path: assert property (
        @(posedge clk) disable iff (1'b0)
        (bsr_mode && !se) |-> (to_core == bsr_data_to_core)
    );

    // Otherwise, to_core selects rcvr_data.
    check_to_core_rcvr_path: assert property (
        @(posedge clk) disable iff (1'b0)
        (!bsr_mode || se) |-> (to_core == rcvr_data)
    );

    // With output enable low, the pad outputs remain in their inactive state.
    check_outputs_when_oe_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (!oe) |-> (!pad_up && pad_dn_l)
    );

    // With output enable high, both pad outputs track data as implemented.
    check_outputs_when_oe_high: assert property (
        @(posedge clk) disable iff (1'b0)
        oe |-> ((pad_up == data) && (pad_dn_l == data))
    );

endmodule