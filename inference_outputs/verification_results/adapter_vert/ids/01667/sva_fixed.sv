module vending_machine_sva (
    input logic button1,
    input logic button2,
    input logic button3,
    input logic change,
    input logic coin,
    input logic product1,
    input logic product2,
    input logic product3,
    input logic b0,
    input logic b1,
    input logic clk_in_1
);

property ValidTickeotid; @(posedge clk_in_1) (button1 | button2 | button3) & ~coin |-> product1 == 1'b1 ; endproperty
assert property (ValidTickeotid);

property ValidTickeotid_2; @(posedge clk_in_1) (button1 | button2 | button3) & ~coin |-> product2 == 1'b1 ; endproperty
assert property (ValidTickeotid_2);

property ValidTickeotid_3; @(posedge clk_in_1) (button1 | button2 | button3) & ~coin |-> product3 == 1'b1 ; endproperty
assert property (ValidTickeotid_3);

property ValidTickeotid_4; @(posedge clk_in_1) (button1 | button2 | button3) & ~coin |-> change == 1'b1 ; endproperty
assert property (ValidTickeotid_4);

property ValidTickeotid_5; @(posedge clk_in_1)  (button1 != 1'b1 && button2 != 1'b1 && button3 != 1'b1)  |-> product1 == 1'b0 ; endproperty
assert property (ValidTickeotid_5);

property ValidTickeotid_6; @(posedge clk_in_1)  (button1 != 1'b1 && button2 != 1'b1 && button3 != 1'b1)  |-> product2 == 1'b0 ; endproperty
assert property (ValidTickeotid_6);

property ValidTickeotid_7; @(posedge clk_in_1)  (button1 != 1'b1 && button2 != 1'b1 && button3 != 1'b1)  |-> product3 == 1'b0 ; endproperty
assert property (ValidTickeotid_7);

property ValidTickeotid_8; @(posedge clk_in_1)  (button1 != 1'b1 && button2 != 1'b1 && button3 != 1'b1)  |-> change == 1'b0 ; endproperty
assert property (ValidTickeotid_8);

endmodule