module vending_machine_sva (
    input logic [1:0] coin,
    input logic [1:0] item,
    input logic dispense,
    input logic vend
);
    // No clock/reset in RTL; combinational logic sampled on any input edge.

    // vend must be LOW when no item is selected.
    check_no_item_selected_forces_vend_low: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        (item == 2'b00) |-> (vend == 1'b0)
    );

    // vend must be LOW when dispense is LOW.
    check_dispense_low_forces_vend_low: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        (!dispense) |-> (vend == 1'b0)
    );

    // vend must be LOW when coin is less than item cost.
    check_insufficient_coin_forces_vend_low: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        ((item == 2'b01) && (coin < 2'b01)) |-> (vend == 1'b0)
    );

    // vend must be LOW when coin is less than item cost.
    check_insufficient_coin_forces_vend_low: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        ((item == 2'b10) && (coin < 2'b10)) |-> (vend == 1'b0)
    );

    // vend must be LOW when coin is less than item cost.
    check_insufficient_coin_forces_vend_low: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        ((item == 2'b11) && (coin < 2'b11)) |-> (vend == 1'b0)
    );

    // vend must be HIGH when item is A and coin is 5 cents and dispense is HIGH.
    check_item_a_valid_inputs_drive_vend_high: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        ((item == 2'b01) && (coin >= 2'b01) && dispense) |-> (vend == 1'b1)
    );

    // vend must be HIGH when item is B and coin is 10 cents and dispense is HIGH.
    check_item_b_valid_inputs_drive_vend_high: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        ((item == 2'b10) && (coin >= 2'b10) && dispense) |-> (vend == 1'b1)
    );

    // vend must be HIGH when item is C and coin is 15 cents and dispense is HIGH.
    check_item_c_valid_inputs_drive_vend_high: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        ((item == 2'b11) && (coin >= 2'b11) && dispense) |-> (vend == 1'b1)
    );

    // vend can be HIGH only when item is A and coin is 5 cents and dispense is HIGH.
    check_vend_high_implies_item_a_valid_inputs: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        vend |-> ((item == 2'b01) && (coin >= 2'b01) && dispense)
    );

    // vend can be HIGH only when item is B and coin is 10 cents and dispense is HIGH.
    check_vend_high_implies_item_b_valid_inputs: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        vend |-> ((item == 2'b10) && (coin >= 2'b10) && dispense)
    );

    // vend can be HIGH only when item is C and coin is 15 cents and dispense is HIGH.
    check_vend_high_implies_item_c_valid_inputs: assert property (
        @(posedge coin[0] or negedge coin[0] or posedge coin[1] or negedge coin[1] or
          posedge item[0] or negedge item[0] or posedge item[1] or negedge item[1] or
          posedge dispense or negedge dispense)
        vend |-> ((item == 2'b11) && (coin >= 2'b11) && dispense)
    );

endmodule