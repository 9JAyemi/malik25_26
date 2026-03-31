// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, IDLE, b00, b01, b10, check_reset_forces_idle, assert, property, posedge, check_reset_clears_outputs, check_idle_outputs_low, disable, iff, check_idle_advances_on_valid_request, check_idle_stays_without_valid_request, check_selected_outputs, check_dispense_implies_selected_state, check_selected_holds_until_dispensed, check_selected_advances_when_dispensed, check_dispensed_outputs, check_return_implies_dispensed_state, check_dispensed_returns_to_idle, check_invalid_state_outputs_safe, inside, check_invalid_state_recovers_to_idle
bind fsm_vending_machine fsm_vending_machine_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .coin_inserted(coin_inserted),
    .item_selected(item_selected),
    .item_dispensed(item_dispensed),
    .dispense_item(dispense_item),
    .return_coin(return_coin),
    .ITEM_SELECTED(item_selected),
    .ITEM_DISPENSED(item_dispensed)
);
