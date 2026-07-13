module vending_machine_sva (
    input logic CLK,
    input logic coin,
    input logic button1,
    input logic button2,
    input logic button3,
    input logic product1,
    input logic product2,
    input logic product3,
    input logic change
);

    // product1 equals button1 & ~coin
    check_product1_func_equiv: assert property (
        @(posedge CLK) product1 == (button1 & ~coin)
    );

    // product2 equals button2 & ~coin
    check_product2_func_equiv: assert property (
        @(posedge CLK) product2 == (button2 & ~coin)
    );

    // product3 equals button3 & ~coin
    check_product3_func_equiv: assert property (
        @(posedge CLK) product3 == (button3 & ~coin)
    );

    // change equals coin
    check_change_equals_coin: assert property (
        @(posedge CLK) change == coin
    );

    // If coin is HIGH, all product outputs must be LOW
    check_coin_high_blocks_products: assert property (
        @(posedge CLK) coin |-> !(product1 | product2 | product3)
    );

    // If any button is pressed with coin LOW, at least one product is HIGH
    check_any_button_no_coin_causes_some_product: assert property (
        @(posedge CLK) (~coin & (button1 | button2 | button3)) |-> (product1 | product2 | product3)
    );

    // product1 HIGH implies button1 is HIGH
    check_product1_implies_button1: assert property (
        @(posedge CLK) product1 |-> button1
    );

    // product2 HIGH implies button2 is HIGH
    check_product2_implies_button2: assert property (
        @(posedge CLK) product2 |-> button2
    );

    // product3 HIGH implies button3 is HIGH
    check_product3_implies_button3: assert property (
        @(posedge CLK) product3 |-> button3
    );

    // Products and change are mutually exclusive
    check_change_and_products_mutex: assert property (
        @(posedge CLK) (product1 | product2 | product3) |-> !change
    );

endmodule