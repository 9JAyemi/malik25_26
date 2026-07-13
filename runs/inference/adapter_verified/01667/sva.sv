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

// Coin high forces change high and all products low.
    check_coin_forces_change: assert property (
        @(posedge clk) coin |-> (change == 1'b1) && (product1 == 1'b0) && (product2 == 1'b0) && (product3 == 1'b0)
    );

// No coin with button1 selects product1 and no change.
    check_button1_selects_product1: assert property (
        @(posedge clk) (!coin && button1 && !button2 && !button3) |-> (change == 1'b0) && (product1 == 1'b1) && (product2 == 1'b0) && (product3 == 1'b0)
    );

// No coin with button2 selects product2 and no change.
    check_button2_selects_product2: assert property (
        @(posedge clk) (!coin && !button1 && button2 && !button3) |-> (change == 1'b0) && (product1 == 1'b0) && (product2 == 1'b1) && (product3 == 1'b0)
    );

// No coin with button3 selects product3 and no change.
    check_button3_selects_product3: assert property (
        @(posedge clk) (!coin && !button1 && !button2 && button3) |-> (change == 1'b0) && (product1 == 1'b0) && (product2 == 1'b0) && (product3 == 1'b1)
    );

// No coin with multiple buttons selects only the first selected product.
    check_multiple_buttons_select_first: assert property (
        @(posedge clk) (!coin && button1 && button2 && !button3) |-> (change == 1'b0) && (product1 == 1'b1) && (product2 == 1'b0) && (product3 == 1'b0)
    );

// No coin with no buttons selected drives no products and no change.
    check_no_buttons_selects_none: assert property (
        @(posedge clk) (!coin && !button1 && !button2 && !button3) |-> (change == 1'b0) && (product1 == 1'b0) && (product2 == 1'b0) && (product3 == 1'b0)
    );

// With coin and any button selected, change is high and products are low.
    check_coin_with_any_button_forces_change: assert property (
        @(posedge clk) (coin && (button1 || button2 || button3)) |-> (change == 1'b1) && (product1 == 1'b0) && (product2 == 1'b0) && (product3 == 1'b0)
    );

// With coin and no button selected, change is high and products are low.
    check_coin_without_buttons_forces_change: assert property (
        @(posedge clk) (coin && !button1 && !button2 && !button3) |-> (change == 1'b1) && (product1 == 1'b0) && (product2 == 1'b0) && (product3 == 1'b0)
    );

endmodule
