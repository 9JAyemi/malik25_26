module vending_machine_sva (
    input logic [1:0] coin,
    input logic [1:0] item,
    input logic       dispense,
    input logic       vend
);
    // Analysis: no clock/reset present; pure combinational logic.
    // Ports: coin[1:0], item[1:0], dispense inputs; vend output.
    // Behavior: vend=0 if item==00; else vend=(coin>=item_cost) && dispense.

    // Item 00: vend must be 0.
    check_item00_vend_zero: assert property (
        @(posedge dispense or posedge coin[0] or posedge coin[1] or posedge item[0] or posedge item[1])
        (item == 2'b00) |-> (vend == 1'b0)
    );

    // Item 01: with dispense and coin>=1, vend must be 1.
    check_item01_dispense_and_coin_implies_vend: assert property (
        @(posedge dispense or posedge coin[0] or posedge coin[1] or posedge item[0] or posedge item[1])
        (item == 2'b01 && dispense && (coin >= 2'b01)) |-> (vend == 1'b1)
    );

    // Item 01: if no dispense or coin<1, vend must be 0.
    check_item01_block_when_insufficient_or_no_dispense: assert property (
        @(posedge dispense or posedge coin[0] or posedge coin[1] or posedge item[0] or posedge item[1])
        (item == 2'b01 && ((!dispense) || (coin < 2'b01))) |-> (vend == 1'b0)
    );

    // Item 10: with dispense and coin>=2, vend must be 1.
    check_item10_dispense_and_coin_implies_vend: assert property (
        @(posedge dispense or posedge coin[0] or posedge coin[1] or posedge item[0] or posedge item[1])
        (item == 2'b10 && dispense && (coin >= 2'b10)) |-> (vend == 1'b1)
    );

    // Item 10: if no dispense or coin<2, vend must be 0.
    check_item10_block_when_insufficient_or_no_dispense: assert property (
        @(posedge dispense or posedge coin[0] or posedge coin[1] or posedge item[0] or posedge item[1])
        (item == 2'b10 && ((!dispense) || (coin < 2'b10))) |-> (vend == 1'b0)
    );

    // Item 11: with dispense and coin>=3, vend must be 1.
    check_item11_dispense_and_coin_implies_vend: assert property (
        @(posedge dispense or posedge coin[0] or posedge coin[1] or posedge item[0] or posedge item[1])
        (item == 2'b11 && dispense && (coin >= 2'b11)) |-> (vend == 1'b1)
    );

    // Item 11: if no dispense or coin<3, vend must be 0.
    check_item11_block_when_insufficient_or_no_dispense: assert property (
        @(posedge dispense or posedge coin[0] or posedge coin[1] or posedge item[0] or posedge item[1])
        (item == 2'b11 && ((!dispense) || (coin < 2'b11))) |-> (vend == 1'b0)
    );

    // Vend high implies dispense high.
    check_vend_implies_dispense: assert property (
        @(posedge vend) dispense
    );

    // Dispense low forces vend low for all items.
    check_dispense_low_forces_vend_low: assert property (
        @(posedge dispense or negedge dispense) (!dispense) |-> (vend == 1'b0)
    );

    // Vend high implies an item is selected (not 00).
    check_vend_implies_item_selected: assert property (
        @(posedge vend) (item != 2'b00)
    );
endmodule