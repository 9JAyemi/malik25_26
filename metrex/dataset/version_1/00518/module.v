
module vending_machine_controller(
    input [1:0] product_sel,
    input [7:0] money_in, // Fix: Increased the width of money_in to accommodate all values
    output reg dispense,
    output reg [5:0] change
);

    // Define the prices of the products
    parameter PRICE_1 = 6'd10; // 50 cents
    parameter PRICE_2 = 6'd15; // 75 cents
    parameter PRICE_3 = 6'd20; // 1 dollar
    parameter PRICE_4 = 6'd25; // 1 dollar 25 cents
    
    // Define the total cost of the selected product
    reg [5:0] total_cost;
    always @(*) begin
        case (product_sel)
            2'b00: total_cost = PRICE_1;
            2'b01: total_cost = PRICE_2;
            2'b10: total_cost = PRICE_3;
            2'b11: total_cost = PRICE_4;
        endcase
    end
    
    // Define the remaining amount of money needed to dispense the product
    reg [6:0] remaining_cost; // Fix: Increased the width of remaining_cost to accommodate all values
    always @(*) begin
        if (money_in < total_cost)
            remaining_cost = total_cost - money_in;
        else
            remaining_cost = 0;
    end
    
    // Define the amount of change to be returned to the user
    reg [5:0] change_due;
    always @(*) begin
        change_due = money_in - total_cost;
    end
    
    // Define the dispense signal
    always @(*) begin
        if (remaining_cost == 0)
            dispense = 1'b1;
        else
            dispense = 1'b0;
    end
    
    // Define the change signal
    always @(*) begin
        if (remaining_cost == 0)
            change = change_due;
        else
            change = 6'b000000;
    end

endmodule