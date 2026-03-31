module vending_machine_sva (
    input logic clk,
    input logic [1:0] coin,
    input logic [1:0] item,
    input logic dispense,
    input logic vend
);

// No item selected forces vend low.
    check_no_item_selected_forces_vend_low: assert property (
        @(posedge clk) (item == 2'b00) |-> (vend == 1'b0)
    );

// Item A requires 5 cents and dispense.
    check_item_a_requires_5c_and_dispense: assert property (
        @(posedge clk) (item == 2'b01) |-> ((coin >= 2'b01) && dispense) == vend
    );

// Item B requires 10 cents and dispense.
    check_item_b_requires_10c_and_dispense: assert property (
        @(posedge clk) (item == 2'b10) |-> ((coin >= 2'b10) && dispense) == vend
    );

// Item C requires 15 cents and dispense.
    check_item_c_requires_15c_and_dispense: assert property (
        @(posedge clk) (item == 2'b11) |-> ((coin >= 2'b11) && dispense) == vend
    );

// vend high implies the selected item's cost and dispense are met.
    check_vend_high_implies_required_inputs: assert property (
        @(posedge clk) vend |-> ((item != 2'b00) && (coin >= item) && dispense)
    );

// With item A selected, 5 cents and dispense together drive vend high.
    check_item_a_grants_vend_when_5c_and_dispense: assert property (
        @(posedge clk) (item == 2'b01 && coin == 2'b01 && dispense) |-> (vend == 1'b1)
    );

// With item B selected, 10 cents and dispense together drive vend high.
    check_item_b_grants_vend_when_10c_and_dispense: assert property (
        @(posedge clk) (item == 2'b10 && coin == 2'b10 && dispense) |-> (vend == 1'b1)
    );

// With item C selected, 15 cents and dispense together drive vend high.
    check_item_c_grants_vend_when_15c_and_dispense: assert property (
        @(posedge clk) (item == 2'b11 && coin == 2'b11 && dispense) |-> (vend == 1'b1)
    );

endmodule
