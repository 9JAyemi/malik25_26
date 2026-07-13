module fsm_vending_machine_sva (
    input logic clk,
    input logic reset,
    input logic coin_inserted,
    input logic [1:0] item_selected,
    input logic item_dispensed,
    input logic dispense_item,
    input logic return_coin,
    input logic [1:0] state
);

    localparam [1:0] IDLE            = 2'b00;
    localparam [1:0] ITEM_SELECTED   = 2'b01;
    localparam [1:0] ITEM_DISPENSED  = 2'b10;

    // Reset holds the FSM in IDLE.
    check_reset_forces_idle: assert property (
        @(posedge clk) reset |-> (state == IDLE)
    );

    // Reset clears both outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |-> (!dispense_item && !return_coin)
    );

    // IDLE drives both outputs low.
    check_idle_outputs_low: assert property (
        @(posedge clk) disable iff (reset)
        (state == IDLE) |-> (!dispense_item && !return_coin)
    );

    // A valid coin and selection moves IDLE to ITEM_SELECTED.
    check_idle_advances_on_valid_request: assert property (
        @(posedge clk) disable iff (reset)
        (state == IDLE && coin_inserted && (item_selected != 2'b00)) |=> (state == ITEM_SELECTED)
    );

    // Without a valid request, IDLE remains IDLE.
    check_idle_stays_without_valid_request: assert property (
        @(posedge clk) disable iff (reset)
        (state == IDLE && !(coin_inserted && (item_selected != 2'b00))) |=> (state == IDLE)
    );

    // ITEM_SELECTED asserts dispense_item and deasserts return_coin.
    check_selected_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state == ITEM_SELECTED) |-> (dispense_item && !return_coin)
    );

    // dispense_item only occurs in ITEM_SELECTED.
    check_dispense_implies_selected_state: assert property (
        @(posedge clk) disable iff (reset)
        dispense_item |-> (state == ITEM_SELECTED)
    );

    // ITEM_SELECTED holds until item_dispensed is asserted.
    check_selected_holds_until_dispensed: assert property (
        @(posedge clk) disable iff (reset)
        (state == ITEM_SELECTED && !item_dispensed) |=> (state == ITEM_SELECTED)
    );

    // item_dispensed advances ITEM_SELECTED to ITEM_DISPENSED.
    check_selected_advances_when_dispensed: assert property (
        @(posedge clk) disable iff (reset)
        (state == ITEM_SELECTED && item_dispensed) |=> (state == ITEM_DISPENSED)
    );

    // ITEM_DISPENSED deasserts dispense_item and asserts return_coin.
    check_dispensed_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (state == ITEM_DISPENSED) |-> (!dispense_item && return_coin)
    );

    // return_coin only occurs in ITEM_DISPENSED.
    check_return_implies_dispensed_state: assert property (
        @(posedge clk) disable iff (reset)
        return_coin |-> (state == ITEM_DISPENSED)
    );

    // ITEM_DISPENSED always returns to IDLE on the next cycle.
    check_dispensed_returns_to_idle: assert property (
        @(posedge clk) disable iff (reset)
        (state == ITEM_DISPENSED) |=> (state == IDLE)
    );

    // An invalid state drives safe outputs.
    check_invalid_state_outputs_safe: assert property (
        @(posedge clk) disable iff (reset)
        !(state inside {IDLE, ITEM_SELECTED, ITEM_DISPENSED}) |-> (!dispense_item && !return_coin)
    );

    // An invalid state recovers to IDLE on the next cycle.
    check_invalid_state_recovers_to_idle: assert property (
        @(posedge clk) disable iff (reset)
        !(state inside {IDLE, ITEM_SELECTED, ITEM_DISPENSED}) |=> (state == IDLE)
    );

endmodule