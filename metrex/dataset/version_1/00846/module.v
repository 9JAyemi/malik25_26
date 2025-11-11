module vending_machine (
    input wire reset,
    input wire clk,
    input wire [1:0] button,
    input wire [1:0] coin,
    output reg [7:0] disp_price,
    output reg [7:0] disp_money,
    output reg [7:0] disp_change
);

    // Define constants
    parameter PRICE_1 = 50;
    parameter PRICE_2 = 75;
    parameter PRICE_3 = 100;
    parameter PRICE_4 = 125;

    // Define state machine states
    localparam IDLE = 2'b00;
    localparam DISP_PRICE = 2'b01;
    localparam INSERT_COIN = 2'b10;
    localparam DISP_CHANGE = 2'b11;

    // Define state machine signals
    reg [1:0] state;
    reg [7:0] price;
    reg [7:0] money;
    reg [7:0] change;
    reg [7:0] coin_value;

    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            state <= IDLE;
            price <= 0;
            money <= 0;
            change <= 0;
            coin_value <= 0;
            disp_price <= 0;
            disp_money <= 0;
            disp_change <= 0;
        end else begin
            case (state)
                IDLE: begin
                    if (button != 2'b00) begin
                        state <= DISP_PRICE;
                        case (button)
                            2'b01: price <= PRICE_1;
                            2'b10: price <= PRICE_2;
                            2'b11: price <= PRICE_3;
                            2'b00: price <= PRICE_4;
                        endcase
                        disp_price <= price;
                    end else begin
                        disp_price <= 0;
                    end
                    disp_money <= money;
                    disp_change <= change;
                end
                DISP_PRICE: begin
                    if (coin != 2'b00) begin
                        state <= INSERT_COIN;
                        case (coin)
                            2'b01: coin_value <= 5;
                            2'b10: coin_value <= 10;
                            2'b11: coin_value <= 25;
                            2'b00: coin_value <= 50;
                        endcase
                        money <= money + coin_value;
                    end else begin
                        disp_price <= price;
                    end
                    disp_money <= money;
                    disp_change <= change;
                end
                INSERT_COIN: begin
                    if (money >= price) begin
                        state <= DISP_CHANGE;
                        change <= money - price;
                        money <= money - price;
                    end else begin
                        coin_value <= 0;
                        state <= DISP_PRICE;
                    end
                    disp_price <= price;
                    disp_money <= money;
                    disp_change <= change;
                end
                DISP_CHANGE: begin
                    if (coin != 2'b00) begin
                        state <= INSERT_COIN;
                        case (coin)
                            2'b01: coin_value <= 5;
                            2'b10: coin_value <= 10;
                            2'b11: coin_value <= 25;
                            2'b00: coin_value <= 50;
                        endcase
                        change <= change + coin_value;
                    end else begin
                        state <= IDLE;
                        price <= 0;
                        money <= 0;
                        change <= 0;
                        coin_value <= 0;
                        disp_price <= 0;
                        disp_money <= 0;
                        disp_change <= 0;
                    end
                    disp_price <= price;
                    disp_money <= money;
                    disp_change <= change;
                end
            endcase
        end
    end

endmodule