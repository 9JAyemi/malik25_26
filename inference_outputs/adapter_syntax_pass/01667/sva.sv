module vending_machine_sva (
    input logic coin,
    input logic button1,
    input logic button2,
    input logic button3,
    input logic product1,
    input logic product2,
    input logic product3,
    input logic change
);

    // change is asserted only when coin is high and no button is selected.
    check_change_definition: assert property (
        @($global_clock) change == (coin & ~((button1 | button2 | button3) & ~coin))
    );

    // product1 is asserted only when button1 is selected and coin is low.
    check_product1_definition: assert property (
        @($global_clock) product1 == ((button1 & ~(button2 | button3)) & ~coin)
    );

    // product2 is asserted only when button2 is selected and coin is low.
    check_product2_definition: assert property (
        @($global_clock) product2 == ((button2 & ~(button1 | button3)) & ~coin)
    );

    // product3 is asserted only when button3 is selected and coin is low.
    check_product3_definition: assert property (
        @($global_clock) product3 == ((button3 & ~(button1 | button2)) & ~coin)
    );

    // change and product1 are never asserted together.
    check_change_excludes_product1: assert property (
        @($global_clock) !(change & product1)
    );

    // change and product2 are never asserted together.
    check_change_excludes_product2: assert property (
        @($global_clock) !(change & product2)
    );

    // change and product3 are never asserted together.
    check_change_excludes_product3: assert property (
        @($global_clock) !(change & product3)
    );

    // product1 and product2 are never asserted together.
    check_product1_excludes_product2: assert property (
        @($global_clock) !(product1 & product2)
    );

    // product1 and product3 are never asserted together.
    check_product1_excludes_product3: assert property (
        @($global_clock) !(product1 & product3)
    );

    // product2 and product3 are never asserted together.
    check_product2_excludes_product3: assert property (
        @($global_clock) !(product2 & product3)
    );

endmodule