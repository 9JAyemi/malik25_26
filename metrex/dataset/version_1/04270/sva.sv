// Drop this SVA block inside the module or bind it to the DUT.
// Focus: synchronous reset behavior, enable semantics, 1-cycle delay register, data integrity, and minimal coverage.

`ifdef ASSERT_ON
    // SVA for delay_reset_controller
    // Assumes synchronous reset: soft_reset = reset || Reset_1
    logic soft_reset;
    always @(*) soft_reset = reset || Reset_1;

    default clocking cb @(posedge CLK_IN); endclocking
    default disable iff (soft_reset)

    // Reset drives zeros (checked on the same cycle)
    assert property (@cb soft_reset |-> ##0 (Out == 0));
    assert property (@cb soft_reset |-> ##0 (In_Delay_out1 == 0));

    // Enable writes Out with In on the same cycle (when not in reset)
    assert property (@cb enb_1_2000_0 |-> ##0 (Out == In));

    // Hold behavior when enable is low
    assert property (@cb !enb_1_2000_0 |-> (Out == $past(Out)));

    // Out can only change due to enable (excluding reset cycles)
    assert property (@cb (Out != $past(Out)) |-> enb_1_2000_0);

    // Delay register captures previous Out (robust across reset boundary)
    assert property (@cb $past(!soft_reset) |-> (In_Delay_out1 == $past(Out)));
    assert property (@cb $rose(!soft_reset) |-> (In_Delay_out1 == 0));

    // Known-value checks after reset is released
    assert property (@cb !$isunknown({Out, In_Delay_out1}));

    // Lightweight coverage
    cover property (@cb soft_reset ##1 !soft_reset ##1 enb_1_2000_0);
    cover property (@cb !soft_reset && enb_1_2000_0 ##1 (Out == In));
    cover property (@cb !soft_reset && !enb_1_2000_0 ##1 (Out == $past(Out)));
`endif