module vending_machine_sva (
    input logic clk,
    input logic coin,
    input logic button1,
    input logic button2,
    input logic button3,
    input logic product1,
    input logic product2,
    input logic product3,
    input logic change
);

    // change is asserted only when coin is high and no valid selection is made.
    check_change_definition: assert property (
        @(posedge clk) change == (coin & ~((button1 | button2 | button3) & ~coin))
    );

    // product1 is asserted only when button1 is selected and coin is low.
    check_product1_definition: assert property (
        @(posedge clk) product1 == ((button1 & ~(button2 | button3)) & ~coin)
    );

    // product2 is asserted only when button2 is selected and coin is low.
    check_product2_definition: assert property (
        @(posedge clk) product2 == ((button2 & ~(button1 | button3)) & ~coin)
    );

    // product3 is asserted only when button3 is selected and coin is low.
    check_product3_definition: assert property (
        @(posedge clk) product3 == ((button3 & ~(button1 | button2)) & ~coin)
    );

    // change and any product output are never asserted together.
    check_change_mutex: assert property (
        @(posedge clk) !(change & (product1 | product2 | product3))
    );

    // With no coin and no valid selection, both change and a product must be low.
    check_no_selection_behavior: assert property (
        @(posedge clk) (~coin & ~(button1 | button2 | button3)) |-> (~change & ~product1 & ~product2 & ~product3)
    );

    // With no coin and a valid selection, change must be low and exactly one product must be high.
    check_valid_selection_behavior: assert property (
        @(posedge clk) (~coin & (button1 | button2 | button3)) |-> (~change & (product1 ^ product2 ^ product3))
    );

    // With coin high and no valid selection, change must be high and no product can be high.
    check_coin_only_behavior: assert property (
        @(posedge clk) (coin & ~(button1 | button2 | button3)) |-> (change & ~product1 & ~product2 & ~product3)
    );

    // With coin high and a valid selection, change must be low and the selected product must be high.
    check_coin_with_selection_behavior: assert property (
        @(posedge clk) (coin & (button1 | button2 | button3)) |-> (~change & ((button1 & product1) | (button2 & product2) | (button3 & product3)))
    );

    // With coin high and no valid selection, the product outputs must be low.
    check_coin_no_selection_product_low: assert property (
        @(posedge clk) (coin & ~(button1 | button2 | button3)) |-> (~product1 & ~product2 & ~product3)
    );

endmodule