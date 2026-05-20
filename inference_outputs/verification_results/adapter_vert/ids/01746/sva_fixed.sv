module vending_machine_sva (
    input logic coin,
    input logic dispense,
    input logic item,
    input logic vend,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ValidCoinForItemeotid; @(posedge clk_in_1) (item) == (2'b00) |-> (vend) == 0 ; endproperty
assert property (ValidCoinForItemeotid);

property ValidCoinForItemAeotid; @(posedge clk_in_1) (item) == (2'b01) &&  (coin >= 2'b01) &&  (dispense) |-> (vend) == 1 ; endproperty
assert property (ValidCoinForItemAeotid);

property ValidCoinForItemBeotid; @(posedge clk_in_1) (item) == (2'b10) &&  (coin >= 2'b10) &&  (dispense) |-> (vend) == 1 ; endproperty
assert property (ValidCoinForItemBeotid);

property ValidCoinForItemCeotid; @(posedge clk_in_1) (item) == (2'b11) &&  (coin >= 2'b11) &&  (dispense) |-> (vend) == 1 ; endproperty
assert property (ValidCoinForItemCeotid);

endmodule