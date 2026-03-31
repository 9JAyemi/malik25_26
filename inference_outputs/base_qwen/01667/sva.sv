```systemverilog
module vending_machine_sva (
    input logic CLK,
    input logic RESETn,
    input logic coin,
    input logic button1,
    input logic button2,
    input logic button3,
    output logic product1,
    output logic product2,
    output logic product3,
    output logic change
);
    // valid_selection is HIGH when a valid button is pressed and no coin is inserted
    property valid_selection_prop;
        @(posedge CLK) disable iff (!RESETn) valid_selection == (button1 | button2 | button3) & ~coin;
    endproperty
    valid_selection_check: assert property (valid_selection_prop) else $error("valid_selection is not correctly calculated");

    // product1 is HIGH when button1 is pressed and valid_selection is HIGH
    property product1_prop;
        @(posedge CLK) disable iff (!RESETn) product1 == (valid_selection & button1);
    endproperty
    product1_check: assert property (product1_prop) else $error("product1 is not correctly calculated");

    // product2 is HIGH when button2 is pressed and valid_selection is HIGH
    property product2_prop;
        @(posedge CLK) disable iff (!RESETn) product2 == (valid_selection & button2);
    endproperty
    product2_check: assert property (product2_prop) else $error("product2 is not correctly calculated");

    // product3 is HIGH when button3 is pressed and valid_selection is HIGH
    property product3_prop;
        @(posedge CLK) disable iff (!RESETn) product3 == (valid_selection & button3);
    endproperty
    product3_check: assert property (product3_prop) else $error("product3 is not correctly calculated");

    // change is HIGH when a coin is inserted and no valid_selection is made
    property change_prop;
        @(posedge CLK) disable iff (!RESETn) change == (coin & ~valid_selection);
    endproperty
    change_check: assert property (change_prop) else $error("change is not correctly calculated");

    // At reset, all outputs should be LOW
    property reset_prop;
        @(posedge CLK) !RESETn |-> (product1 == 1'b0) && (product2 == 1'b0) && (product3 == 1'b0) && (change == 1'b0);
    endproperty
    reset_check: assert property (reset_prop) else $error("Outputs are not correctly reset at reset");

endmodule
```