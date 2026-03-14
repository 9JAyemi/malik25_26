module der_misc_sva (
    input  logic        de_clk,
    input  logic        hb_clk,
    input  logic        prst,
    input  logic        cr_pulse,
    input  logic [1:0]  ps_sel_2,
    input  logic        bc_co,
    input  logic [31:0] mf_sorg_2,
    input  logic [31:0] mf_dorg_2,
    input  logic [1:0]  apat_1,
    input  logic        sd_selector,
    input  logic        prst_1,
    input  logic        hb_ca_rdy,
    input  logic        de_ca_rdy,
    input  logic        ps16s_2,
    input  logic        ps565s_2,
    input  logic [31:0] de_sorg_2,
    input  logic [31:0] de_dorg_2,
    input  logic [27:0] sorg_2,
    input  logic [27:0] dorg_2,
    input  logic        or_apat_1
);
    // prst_1 is a de_clk-registered copy of prst (1-cycle delay).
    check_prst_1_registers_prst: assert property (
        @(posedge de_clk) disable iff (prst) prst_1 == $past(prst)
    );

    // or_apat_1 is the reduction-OR of apat_1.
    check_or_apat_1_reduce: assert property (
        @(posedge de_clk) disable iff (prst) or_apat_1 == (|apat_1)
    );

    // ps16s_2 decodes ps_sel_2 == 2'b01.
    check_ps16s_decode: assert property (
        @(posedge de_clk) disable iff (prst) ps16s_2 == (~ps_sel_2[1] & ps_sel_2[0])
    );

    // ps565s_2 decodes ps_sel_2 == 2'b11.
    check_ps565s_decode: assert property (
        @(posedge de_clk) disable iff (prst) ps565s_2 == (&ps_sel_2)
    );

    // The two decodes are mutually exclusive.
    check_ps_decode_mutex: assert property (
        @(posedge de_clk) disable iff (prst) !(ps16s_2 && ps565s_2)
    );

    // hb_ca_rdy is constantly HIGH.
    check_hb_ca_rdy_const_high: assert property (
        @(posedge de_clk) disable iff (prst) hb_ca_rdy == 1'b1
    );

    // de_ca_rdy is constantly HIGH.
    check_de_ca_rdy_const_high: assert property (
        @(posedge de_clk) disable iff (prst) de_ca_rdy == 1'b1
    );

    // de_sorg_2 passes mf_sorg_2 when sd_selector is 1.
    check_de_sorg_when_sel1: assert property (
        @(posedge de_clk) disable iff (prst) sd_selector |-> (de_sorg_2 == mf_sorg_2)
    );

    // de_sorg_2 is zero when sd_selector is 0.
    check_de_sorg_when_sel0: assert property (
        @(posedge de_clk) disable iff (prst) !sd_selector |-> (de_sorg_2 == 32'b0)
    );

    // de_dorg_2 passes mf_dorg_2 when sd_selector is 1.
    check_de_dorg_when_sel1: assert property (
        @(posedge de_clk) disable iff (prst) sd_selector |-> (de_dorg_2 == mf_dorg_2)
    );

    // de_dorg_2 is zero when sd_selector is 0.
    check_de_dorg_when_sel0: assert property (
        @(posedge de_clk) disable iff (prst) !sd_selector |-> (de_dorg_2 == 32'b0)
    );

    // sorg_2 equals {6'h0, mf_sorg_2[25:4]} when sd_selector is 0.
    check_sorg2_when_sel0: assert property (
        @(posedge de_clk) disable iff (prst) !sd_selector |-> (sorg_2 == {6'h0, mf_sorg_2[25:4]})
    );

    // sorg_2 is zero when sd_selector is 1.
    check_sorg2_when_sel1: assert property (
        @(posedge de_clk) disable iff (prst) sd_selector |-> (sorg_2 == 28'b0)
    );

    // dorg_2 equals {6'h0, mf_dorg_2[25:4]} when sd_selector is 0.
    check_dorg2_when_sel0: assert property (
        @(posedge de_clk) disable iff (prst) !sd_selector |-> (dorg_2 == {6'h0, mf_dorg_2[25:4]})
    );

    // dorg_2 is zero when sd_selector is 1.
    check_dorg2_when_sel1: assert property (
        @(posedge de_clk) disable iff (prst) sd_selector |-> (dorg_2 == 28'b0)
    );
endmodule