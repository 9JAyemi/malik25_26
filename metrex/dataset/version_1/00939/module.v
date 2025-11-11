module vending_machine(
    input clk, 
    input reset, 
    input [1:0] coin, 
    input [3:0] product, 
    output reg dispense, 
    output reg [1:0] change, 
    output reg ready
);

reg [3:0] product_price;
reg [7:0] coins_inserted;
reg [1:0] coins_returned;
reg dispense_product;
reg return_coins;
reg ready_state;

always @(*) begin
    case(product)
        5'd5: product_price = 5;
        5'd6: product_price = 10;
        5'd7: product_price = 15;
        5'd8: product_price = 20;
        5'd9: product_price = 25;
        5'd10: product_price = 30;
        5'd11: product_price = 35;
        5'd12: product_price = 40;
        5'd13: product_price = 45;
        5'd14: product_price = 50;
        5'd15: product_price = 55;
        5'd16: product_price = 60;
        5'd17: product_price = 65;
        5'd18: product_price = 70;
        5'd19: product_price = 75;
        5'd20: product_price = 80;
        5'd21: product_price = 85;
        5'd22: product_price = 90;
        5'd23: product_price = 95;
        5'd24: product_price = 100;
        default: product_price = 0;
    endcase;
end

always @(posedge clk or posedge reset) begin
    if(reset) begin
        coins_inserted <= 0;
        coins_returned <= 0;
        dispense_product <= 0;
        return_coins <= 0;
        ready_state <= 1;
    end else begin
        if(coin == 2'b00) begin // 1 cent
            coins_inserted <= coins_inserted + 1;
        end else if(coin == 2'b01) begin // 5 cents
            coins_inserted <= coins_inserted + 5;
        end else if(coin == 2'b10) begin // 10 cents
            coins_inserted <= coins_inserted + 10;
        end else if(coin == 2'b11) begin // 25 cents
            coins_inserted <= coins_inserted + 25;
        end
        
        if(coins_inserted >= product_price && ready_state == 1) begin
            dispense_product <= 1;
            coins_returned <= coins_inserted - product_price;
            coins_inserted <= 0;
            ready_state <= 0;
        end else if(product_price > coins_inserted) begin
            return_coins <= coin;
        end
    end
end

always @(*) begin
    dispense = dispense_product;
    change = coins_returned;
    ready = ready_state;
end

endmodule