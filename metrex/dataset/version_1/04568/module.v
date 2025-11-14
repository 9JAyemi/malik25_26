
module digital_clock(clk, reset, hours, minutes, seg, an);

    parameter CLK_FREQ = 50_000_000; // 50 MHz clock frequency
    parameter MIN_FREQ = 60; // 60 seconds in a minute
    parameter HOUR_FREQ = 24; // 24 hours in a day
    parameter BCD_WIDTH = 5; // BCD format is 5 bits wide
    parameter SEG_WIDTH = 7; // 7 segments in a seven-segment display
    parameter DISP_WIDTH = 4; // 4 seven-segment displays

    input clk;
    input reset;
    input [BCD_WIDTH-1:0] hours;
    input [BCD_WIDTH-1:0] minutes;
    output reg [SEG_WIDTH*DISP_WIDTH-1:0] seg;
    output reg [DISP_WIDTH-1:0] an;

    reg [BCD_WIDTH-1:0] hours_reg;
    reg [BCD_WIDTH-1:0] minutes_reg; // reduced to 5 bit to hold the carry bit

    always @(posedge clk) begin
        if (reset) begin
            // reset to 00:00:00
            hours_reg <= 5'b00000;
            minutes_reg <= 5'b00000;
            seg <= {28{1'b0}};
            an <= 4'b1111;
        end else begin
            // update time every minute
            minutes_reg <= minutes_reg + 1'b1;
            if (minutes_reg[BCD_WIDTH-1:0] == 5'b0101_10) begin // 60 in BCD
                minutes_reg <= 5'b00000;
                hours_reg <= hours_reg + 1'b1;
                if (hours_reg[BCD_WIDTH-1:0] == 5'd24) begin // 24 in BCD
                    hours_reg <= 5'b00000;
                end
            end

            // update display
            case (an)
                4'b1110: seg <= {7'b1111110, 7'b0000000, 7'b0000000, 7'b0000000}; // right-most display
                4'b1101: seg <= {7'b1111110, 7'b1111110, 7'b0000000, 7'b0000000}; // second-right-most display
                4'b1011: seg <= {7'b1111110, 7'b1111110, 7'b1111110, 7'b0000000}; // second-left-most display
                4'b0111: seg <= {7'b1111110, 7'b1111110, 7'b1111110, 7'b1111110}; // left-most display
                default: seg <= {28{1'b0}};
            endcase

            // set active display
            case (an)
                4'b1110: an <= 4'b1101;
                4'b1101: an <= 4'b1011;
                4'b1011: an <= 4'b0111;
                4'b0111: an <= 4'b1110;
                default: an <= 4'b1110;
            endcase
        end
    end

endmodule