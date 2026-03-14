module scan_chain_interface_sva (
    input logic ctu_tst_pre_grst_l,
    input logic arst_l,
    input logic global_shift_enable,
    input logic ctu_tst_scan_disable,
    input logic ctu_tst_scanmode,
    input logic ctu_tst_macrotest,
    input logic ctu_tst_short_chain,
    input logic long_chain_so_0,
    input logic short_chain_so_0,
    input logic long_chain_so_1,
    input logic short_chain_so_1,
    input logic long_chain_so_2,
    input logic short_chain_so_2,
    input logic mux_drive_disable,
    input logic mem_write_disable,
    input logic sehold,
    input logic se,
    input logic testmode_l,
    input logic mem_bypass,
    input logic so_0,
    input logic so_1,
    input logic so_2
);
    // No explicit clock in RTL; sample on posedge of global_shift_enable.
    // Active-low reset: ctu_tst_pre_grst_l (arst_l is unused).
    // Purely combinational logic; assertions check combinational definitions.

    ///// Direct signal definitions /////
    // se equals global_shift_enable.
    check_se_equals_gse: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l) se == global_shift_enable
    );
    // testmode_l is inverse of ctu_tst_scanmode.
    check_testmode_l_inverse: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l) testmode_l == ~ctu_tst_scanmode
    );
    // mem_bypass equals ~ctu_tst_macrotest & ~testmode_l.
    check_mem_bypass_def: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l) mem_bypass == (~ctu_tst_macrotest & ~testmode_l)
    );
    // sehold equals ctu_tst_macrotest & ~se.
    check_sehold_def: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l) sehold == (ctu_tst_macrotest & ~se)
    );
    // mem_write_disable equals ~ctu_tst_pre_grst_l | se.
    check_mem_write_disable_def: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l) mem_write_disable == (~ctu_tst_pre_grst_l | se)
    );
    // mux_drive_disable equals ~ctu_tst_pre_grst_l | short_chain_select | se.
    check_mux_drive_disable_def: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l)
            mux_drive_disable == (~ctu_tst_pre_grst_l |
                                  (ctu_tst_short_chain & ~testmode_l & ~(ctu_tst_scan_disable & se)) |
                                  se)
    );

    ///// Scan-out mux selection /////
    // so_0 selects between short/long chain based on short_chain_select.
    check_so0_mux: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l)
            so_0 == ((ctu_tst_short_chain & ~testmode_l & ~(ctu_tst_scan_disable & se)) ? short_chain_so_0 : long_chain_so_0)
    );
    // so_1 selects between short/long chain based on short_chain_select.
    check_so1_mux: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l)
            so_1 == ((ctu_tst_short_chain & ~testmode_l & ~(ctu_tst_scan_disable & se)) ? short_chain_so_1 : long_chain_so_1)
    );
    // so_2 selects between short/long chain based on short_chain_select.
    check_so2_mux: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l)
            so_2 == ((ctu_tst_short_chain & ~testmode_l & ~(ctu_tst_scan_disable & se)) ? short_chain_so_2 : long_chain_so_2)
    );

    ///// Derived implications (from direct definitions) /////
    // When testmode_l is HIGH, mem_bypass must be LOW.
    check_testmode_blocks_mem_bypass: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l) testmode_l |-> (mem_bypass == 1'b0)
    );
    // When se is HIGH, sehold must be LOW.
    check_shift_disables_sehold: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l) se |-> (sehold == 1'b0)
    );
    // mem_write_disable implies mux_drive_disable (mux_disable = memw_disable | short_chain_select).
    check_memw_implies_mux_disable: assert property (
        @(posedge global_shift_enable) disable iff (!ctu_tst_pre_grst_l) mem_write_disable |-> mux_drive_disable
    );
endmodule