
module counter_display(
    input CLOCK_50, // 50 MHz FPGA Clock
    input [1:0] KEY, // Pushbutton Keys
    input [5:0] SW, // DIP Switches
    output [6:0] HEX0, HEX1, HEX2, HEX3 // Seven-Segment Displays
);

    wire enable;
    wire [15:0] hexDigits;
    wire [3:0] countValue;

    // Instantiate keyPressed module
    keyPressed K1 ( // Module instantiation with correct module name.
        .clock(CLOCK_50),
        .reset(KEY[0]),
        .enable_in(KEY[1]),
        .enable_out(enable)
    );

    // Instantiate counter16bit module
    counter16bit C1 ( // Module instantiation with correct module name.
        .clock(CLOCK_50),
        .enable(enable),
        .clear(KEY[0]),
        .disp(SW[5]),
        .dir(SW[4]),
        .countValue(countValue),
        .outputValue(hexDigits)
    );

    // Instantiate seven-segment display drivers
    sevenSegmentDecoder S0 (// Module instantiation with correct module name.
        .digit(hexDigits[3:0]),
        .drivers(HEX0)
    );
    sevenSegmentDecoder S1 ( // Module instantiation with correct module name.
        .digit(hexDigits[7:4]),
        .drivers(HEX1)
    );
    sevenSegmentDecoder S2 ( // Module instantiation with correct module name.
        .digit(hexDigits[11:8]),
        .drivers(HEX2)
    );
    sevenSegmentDecoder S3 ( // Module instantiation with correct module name.
        .digit(hexDigits[15:12]),
        .drivers(HEX3)
    );

endmodule

module keyPressed(
    input clock,
    input reset,
    input enable_in,
    output reg enable_out
);

    always @ (posedge clock) begin
        if (reset) begin
            enable_out <= 0;
        end else if (enable_in) begin
            enable_out <= 1;
        end else begin
            enable_out <= 0;
        end
    end

endmodule

module counter16bit(
    input clock,
    input enable,
    input clear,
    input disp,
    input dir, // Corrected typo
    output reg [3:0] countValue,
    output reg [15:0] outputValue
);

    always @ (posedge clock) begin
        if (clear) begin
            countValue <= 0;
            outputValue <= 0;
        end else if (enable) begin
            if (dir) begin
                countValue <= countValue - 1;
            end else begin
                countValue <= countValue + 1;
            end
            outputValue <= {disp, countValue};
        end
    end

endmodule

module sevenSegmentDecoder(
    input [3:0] digit,
    output reg [6:0] drivers
);

    always @ (digit) begin
        case (digit)
            4'b0000: drivers = 7'b1000000; // 0
            4'b0001: drivers = 7'b1111001; // 1
            4'b0010: drivers = 7'b0100100; // 2
            4'b0011: drivers = 7'b0110000; // 3
            4'b0100: drivers = 7'b0011001; // 4
            4'b0101: drivers = 7'b0010010; // 5
            4'b0110: drivers = 7'b0000010; // 6
            4'b0111: drivers = 7'b1111000; // 7
            4'b1000: drivers = 7'b0000000; // 8
            4'b1001: drivers = 7'b0010000; // 9
            default: drivers = 7'b1111111; // Error
        endcase
    end

endmodule
