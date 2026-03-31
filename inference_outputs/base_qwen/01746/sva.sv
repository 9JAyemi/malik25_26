```systemverilog
module vending_machine_sva (
    input logic [1:0] coin,
    input logic [1:0] item,
    input logic dispense,
    output logic vend
);
    ///// Coin and item selection /////
    // vend can only be HIGH when a valid item is selected and the coin is sufficient.
    vend_valid: assert property (
        @(posedge CLK) disable iff (!RESETn) vend |-> (item != 2'b00) && (coin >= item)
    );
    // vend can only be LOW when no item is selected or the coin is insufficient.
    vend_invalid: assert property (
        @(posedge CLK) disable iff (!RESETn) !vend |-> (item == 2'b00) || (coin < item)
    );
    ///// Device reset /////
    // At reset assertion, vend must be LOW.
    reset: assert property (
        @(posedge CLK) !RESETn |-> !vend
    );
endmodule
```