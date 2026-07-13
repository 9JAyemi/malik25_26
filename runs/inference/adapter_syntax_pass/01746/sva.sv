module vending_machine_sva (
    input logic [1:0] coin,
    input logic [1:0] item,
    input logic dispense,
    input logic vend
);

    // No item selected forces vend low.
    check_no_item_selected: assert property (
        @($global_clock) (item == 2'b00) |-> (vend == 1'b0)
    );

    // Item A requires a 5-cent coin and dispense.
    check_item_a_selection: assert property (
        @($global_clock) ((item == 2'b01) && (coin >= 2'b01) && dispense) |-> (vend == 1'b1)
    );

    // Item B requires a 10-cent coin and dispense.
    check_item_b_selection: assert property (
        @($global_clock) ((item == 2'b10) && (coin >= 2'b10) && dispense) |-> (vend == 1'b1)
    );

    // Item C requires a 15-cent coin and dispense.
    check_item_c_selection: assert property (
        @($global_clock) ((item == 2'b11) && (coin >= 2'b11) && dispense) |-> (vend == 1'b1)
    );

    // vend can only be high for item A with a 5-cent coin and dispense.
    check_vend_implies_item_a: assert property (
        @($global_clock) vend |-> ((item == 2'b01) && (coin >= 2'b01) && dispense)
    );

    // vend can only be high for item B with a 10-cent coin and dispense.
    check_vend_implies_item_b: assert property (
        @($global_clock) vend |-> ((item == 2'b10) && (coin >= 2'b10) && dispense)
    );

    // vend can only be high for item C with a 15-cent coin and dispense.
    check_vend_implies_item_c: assert property (
        @($global_clock) vend |-> ((item == 2'b11) && (coin >= 2'b11) && dispense)
    );

endmodule