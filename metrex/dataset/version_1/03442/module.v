
module VerilogModule (
    input CLOCK_27,
    input CLOCK_50,
    input [3:0] KEY,
    input [17:0] SW,
    output [6:0] HEX0,
    output [6:0] HEX1,
    output [6:0] HEX2,
    output [6:0] HEX3,
    output [6:0] HEX4,
    output [6:0] HEX5,
    output [6:0] HEX6,
    output [6:0] HEX7,
    output [8:0] LEDG,
    output [17:0] LEDR,
    output UART_TXD,
    input UART_RXD,
    inout [7:0] LCD_DATA,
    output LCD_ON,
    output LCD_BLON,
    output LCD_RW,
    output LCD_EN,
    output LCD_RS,
    inout [35:0] GPIO_0,
    inout [35:0] GPIO_1
);

    reg [15:0] d0, d1, d2, d3, d4;
    reg [17:0] LEDR;
    reg [8:0] LEDG;

    // Store values of DPDT switch in registers
    always @(posedge KEY[2]) begin
        case(SW[17:16])
            0: d0 <= SW[15:0];
            1: d1 <= SW[15:0];
            2: d2 <= SW[15:0];
            default: d3 <= SW[15:0];
        endcase
    end

    // Add value of d0 to d4 when push button is pressed
    always @(posedge CLOCK_27) begin
        if(!KEY[0]) begin
            d4 <= 0;
        end else begin
            d4 <= d4 + d0;
        end
    end

    // Output values of d0, d1, d2, d3, and d4 to 7-segment display
    assign HEX0 = d0;
    assign HEX1 = d1;
    assign HEX2 = d2;
    assign HEX3 = d3;
    assign HEX4 = d4;
    assign HEX5 = 7'b1111111;
    assign HEX6 = 7'b1111111;
    assign HEX7 = 7'b1111111;

    // Output values of d0, d1, d2, d3, and d4 to UART transmitter
    assign UART_TXD = {d0, d1, d2, d3, d4};

    // Display values of d0, d1, d2, d3, and d4 on LCD module
    assign LCD_ON = 1'b1;
    assign LCD_BLON = 1'b1;
    assign LCD_RW = 1'b0;
    assign LCD_EN = 1'b1;
    assign LCD_RS = 1'b1;

    // Drive LEDR
    always @(posedge CLOCK_27) begin
        LEDR <= d0;
    end

    // Drive LEDG
    always @(posedge CLOCK_27) begin
        LEDG <= 9'b111111111;
    end

endmodule