module hi_read_tx_sva (
    input logic pck0,
    input logic ck_1356meg,
    input logic ck_1356megb,
    input logic pwr_lo,
    input logic pwr_hi,
    input logic pwr_oe1,
    input logic pwr_oe2,
    input logic pwr_oe3,
    input logic pwr_oe4,
    input logic [7:0] adc_d,
    input logic adc_clk,
    input logic ssp_frame,
    input logic ssp_din,
    input logic ssp_dout,
    input logic ssp_clk,
    input logic cross_hi,
    input logic cross_lo,
    input logic dbg,
    input logic shallow_modulation
);

    // adc_clk must mirror ck_1356meg.
    check_adc_clk_equals_ck: assert property (
        @(posedge ck_1356meg) (adc_clk == ck_1356meg)
    );

    // dbg must mirror ssp_din.
    check_dbg_mirrors_ssp_din: assert property (
        @(posedge ck_1356meg) (dbg == ssp_din)
    );

    // pwr_lo is tied low.
    check_pwr_lo_const_zero: assert property (
        @(posedge ck_1356meg) (pwr_lo == 1'b0)
    );

    // pwr_oe4 is tied low.
    check_pwr_oe4_const_zero: assert property (
        @(posedge ck_1356meg) (pwr_oe4 == 1'b0)
    );

    // In shallow_modulation, pwr_hi follows ck_1356megb.
    check_pwr_hi_shallow_mode: assert property (
        @(posedge ck_1356meg) shallow_modulation |-> (pwr_hi == ck_1356megb)
    );

    // In deep modulation (not shallow) with ssp_dout==0, pwr_hi must be 0.
    check_pwr_hi_deep_mode_dout0_zero: assert property (
        @(posedge ck_1356meg) (!shallow_modulation && (ssp_dout == 1'b0)) |-> (pwr_hi == 1'b0)
    );

    // In deep modulation (not shallow) with ssp_dout==1, pwr_hi follows ck_1356megb.
    check_pwr_hi_deep_mode_dout1_ck: assert property (
        @(posedge ck_1356meg) (!shallow_modulation && (ssp_dout == 1'b1)) |-> (pwr_hi == ck_1356megb)
    );

    // In shallow_modulation, pwr_oe[1:3] are the inverse of ssp_dout.
    check_pwr_oe_shallow_mode_invert_dout: assert property (
        @(posedge ck_1356meg) shallow_modulation |-> ((pwr_oe1 == ~ssp_dout) && (pwr_oe2 == ~ssp_dout) && (pwr_oe3 == ~ssp_dout))
    );

    // In deep modulation (not shallow), pwr_oe[1:3] are all zero.
    check_pwr_oe_deep_mode_zero: assert property (
        @(posedge ck_1356meg) (!shallow_modulation) |-> ((pwr_oe1 == 1'b0) && (pwr_oe2 == 1'b0) && (pwr_oe3 == 1'b0))
    );

    // pwr_oe1, pwr_oe2, and pwr_oe3 are always equal.
    check_pwr_oe_triple_equal: assert property (
        @(posedge ck_1356meg) (pwr_oe1 == pwr_oe2) && (pwr_oe2 == pwr_oe3)
    );

    // ssp_frame is stable across the posedge of ssp_clk (it only updates on ssp_clk negedge).
    check_ssp_frame_stable_on_posedge_ssp_clk: assert property (
        @(posedge ssp_clk) (ssp_frame == $past(ssp_frame))
    );

    // ssp_din is stable across the posedge of adc_clk (it only updates on adc_clk negedge).
    check_ssp_din_stable_on_posedge_adc_clk: assert property (
        @(posedge adc_clk) (ssp_din == $past(ssp_din))
    );

    // ssp_frame changes only when ssp_clk falls (hi_byte_div updates on ssp_clk negedge).
    check_ssp_frame_changes_only_on_fall_ssp_clk: assert property (
        @(posedge ck_1356meg) $changed(ssp_frame) |-> $fell(ssp_clk)
    );

    // ssp_clk does not change on consecutive posedges of ck_1356meg (it is a divided clock).
    check_ssp_clk_not_change_consecutive_cycles: assert property (
        @(posedge ck_1356meg) $changed(ssp_clk) |=> !$changed(ssp_clk)
    );

endmodule