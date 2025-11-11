module vending_machine(
    input clk, // clock signal
    input rst, // reset signal
    input start, // start signal to initiate transaction
    input cancel, // cancel signal to cancel transaction
    input [1:0] coin, // input for coin values (00 - no coin, 01 - 5 cents, 10 - 10 cents, 11 - 25 cents)
    output reg [6:0] display, // 7-segment display output for amount inserted (max value 99 cents)
    output reg [1:0] dispense // output for item selection (00 - no item, 01 - item 1, 10 - item 2, 11 - item 3)
    );

    reg [6:0] amount_inserted = 0;
    reg [1:0] item_selected = 0;
    reg [6:0] item_price_1 = 25;
    reg [6:0] item_price_2 = 50;
    reg [6:0] item_price_3 = 75;

    always @(posedge clk) begin
        if (rst) begin
            amount_inserted <= 0;
            item_selected <= 0;
            display <= 0;
            dispense <= 0;
        end else if (start) begin
            if (amount_inserted + coin <= 99) begin
                amount_inserted <= amount_inserted + coin;
                display <= amount_inserted;
            end else begin
                display <= 99;
            end
        end else if (cancel) begin
            amount_inserted <= 0;
            display <= 0;
        end else if (amount_inserted >= item_price_1 && item_selected == 0) begin
            item_selected <= 1;
            amount_inserted <= amount_inserted - item_price_1;
            display <= 0;
            dispense <= item_selected;
        end else if (amount_inserted >= item_price_2 && item_selected == 0) begin
            item_selected <= 2;
            amount_inserted <= amount_inserted - item_price_2;
            display <= 0;
            dispense <= item_selected;
        end else if (amount_inserted >= item_price_3 && item_selected == 0) begin
            item_selected <= 3;
            amount_inserted <= amount_inserted - item_price_3;
            display <= 0;
            dispense <= item_selected;
        end else begin
            display <= amount_inserted;
            dispense <= 0;
        end
    end

endmodule