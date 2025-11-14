module vending_machine_controller(
    input clk,
    input rst,
    input button_A,
    input button_B,
    input button_C,
    input coin,
    output reg dispense_X,
    output reg dispense_Y,
    output reg dispense_Z,
    output reg [23:0] display,
    output reg button_A_enable,
    output reg button_B_enable,
    output reg button_C_enable
);

    // Define constants
    parameter PRICE = 150; // Price of each product in cents
    parameter MAX_STOCK = 5; // Maximum stock of each product
    
    // Define state variables
    reg [1:0] state;
    reg [2:0] inventory;
    reg [23:0] total_money;
    
    // Define state machine states
    parameter [1:0] IDLE = 2'b00;
    parameter [1:0] DISPENSING = 2'b01;
    parameter [1:0] COIN_INSERTED = 2'b10;
    
    // Define state machine transitions and actions
    always @(posedge clk) begin
        if (rst) begin
            state <= IDLE;
            inventory <= {MAX_STOCK, MAX_STOCK, MAX_STOCK};
            total_money <= 0;
            dispense_X <= 0;
            dispense_Y <= 0;
            dispense_Z <= 0;
            button_A_enable <= 1;
            button_B_enable <= 1;
            button_C_enable <= 1;
        end else begin
            case (state)
                IDLE: begin
                    if (button_A && inventory[0] > 0) begin
                        state <= DISPENSING;
                        dispense_X <= 1;
                        inventory[0] <= inventory[0] - 1;
                        total_money <= total_money + PRICE;
                    end else if (button_B && inventory[1] > 0) begin
                        state <= DISPENSING;
                        dispense_Y <= 1;
                        inventory[1] <= inventory[1] - 1;
                        total_money <= total_money + PRICE;
                    end else if (button_C && inventory[2] > 0) begin
                        state <= DISPENSING;
                        dispense_Z <= 1;
                        inventory[2] <= inventory[2] - 1;
                        total_money <= total_money + PRICE;
                    end else if (coin) begin
                        state <= COIN_INSERTED;
                        total_money <= total_money + 100; // Add coin value to total money
                    end
                end
                DISPENSING: begin
                    if (!button_A && !button_B && !button_C) begin
                        state <= IDLE;
                        dispense_X <= 0;
                        dispense_Y <= 0;
                        dispense_Z <= 0;
                    end
                end
                COIN_INSERTED: begin
                    if (button_A && inventory[0] > 0) begin
                        state <= DISPENSING;
                        dispense_X <= 1;
                        inventory[0] <= inventory[0] - 1;
                        total_money <= total_money + PRICE;
                    end else if (button_B && inventory[1] > 0) begin
                        state <= DISPENSING;
                        dispense_Y <= 1;
                        inventory[1] <= inventory[1] - 1;
                        total_money <= total_money + PRICE;
                    end else if (button_C && inventory[2] > 0) begin
                        state <= DISPENSING;
                        dispense_Z <= 1;
                        inventory[2] <= inventory[2] - 1;
                        total_money <= total_money + PRICE;
                    end else if (!coin) begin
                        state <= IDLE;
                    end
                end
            endcase
            
            // Update button enable signals based on inventory levels
            button_A_enable <= (inventory[0] > 0);
            button_B_enable <= (inventory[1] > 0);
            button_C_enable <= (inventory[2] > 0);
            
            // Update display output
            display <= {7'b1111110, 7'b1111110, 7'b1111110}; // Default to showing "888"
            if (state == COIN_INSERTED) begin
                display <= {7'b0000110, 7'b0000000, 7'b0000000} + (total_money / 10); // Show total money in dollars
            end else begin
                display[0] <= 7'b1110000 - (inventory[0] * 7); // Show inventory level for product X
                display[1] <= 7'b1110000 - (inventory[1] * 7); // Show inventory level for product Y
                display[2] <= 7'b1110000 - (inventory[2] * 7); // Show inventory level for product Z
            end
        end
    end
    
endmodule