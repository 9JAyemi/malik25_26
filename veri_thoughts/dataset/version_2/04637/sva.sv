module PAD_BANK2_sva (
    input logic PAD,
    input logic PADIN,
    input logic PADOUT,
    input logic PADOEN,
    input logic PAD_drv_reg
);

    // PAD_drv_reg is a combinational copy of PADOUT.
    check_drv_reg_matches_padout: assert property (
        @($global_clock) PAD_drv_reg == PADOUT
    );

    // PADIN is driven directly from PAD_drv_reg.
    check_padin_matches_drv_reg: assert property (
        @($global_clock) PADIN == PAD_drv_reg
    );

    // PADIN always reflects PADOUT.
    check_padin_matches_padout: assert property (
        @($global_clock) PADIN == PADOUT
    );

    // A PADOUT change propagates to PAD_drv_reg.
    check_drv_reg_changes_with_padout: assert property (
        @($global_clock) (!$initstate && $changed(PADOUT)) |-> $changed(PAD_drv_reg)
    );

    // A PADOUT change propagates to PADIN.
    check_padin_changes_with_padout: assert property (
        @($global_clock) (!$initstate && $changed(PADOUT)) |-> $changed(PADIN)
    );

    // PADOEN alone does not affect PAD_drv_reg.
    check_drv_reg_ignores_padoen_changes: assert property (
        @($global_clock) (!$initstate && $changed(PADOEN) && $stable(PADOUT)) |-> $stable(PAD_drv_reg)
    );

    // PADOEN alone does not affect PADIN.
    check_padin_ignores_padoen_changes: assert property (
        @($global_clock) (!$initstate && $changed(PADOEN) && $stable(PADOUT)) |-> $stable(PADIN)
    );

    // PAD changes do not feed back into PAD_drv_reg.
    check_drv_reg_ignores_pad_changes: assert property (
        @($global_clock) (!$initstate && $changed(PAD) && $stable(PADOUT)) |-> $stable(PAD_drv_reg)
    );

    // PAD changes do not feed back into PADIN.
    check_padin_ignores_pad_changes: assert property (
        @($global_clock) (!$initstate && $changed(PAD) && $stable(PADOUT)) |-> $stable(PADIN)
    );

endmodule