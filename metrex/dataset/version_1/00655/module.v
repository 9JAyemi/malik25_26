
module top_module (
    input clk,
    input sync_reset, // Synchronous active-high reset
    input async_reset, // Asynchronous active-high reset
    output reg [3:1] ena, // Enable signals for digits [3:1]
    output reg [15:0] q // 4-digit BCD output
);

reg [3:0] johnson; // Johnson counter
reg [3:0] count; // Counter for each digit
reg [3:0] bcd; // BCD value for each digit

// Decoder for generating BCD output
always @ (count)
    case (count)
        4'b0000: bcd = 4'b0000;
        4'b0001: bcd = 4'b0001;
        4'b0010: bcd = 4'b0010;
        4'b0011: bcd = 4'b0011;
        4'b0100: bcd = 4'b0100;
        4'b0101: bcd = 4'b0101;
        4'b0110: bcd = 4'b0110;
        4'b0111: bcd = 4'b0111;
        4'b1000: bcd = 4'b1000;
        4'b1001: bcd = 4'b1001;
        default: bcd = 4'b0000;
    endcase

// Control logic for enabling each digit separately
always @ (johnson)
    case (johnson)
        4'b0001: ena = 3'b100;
        4'b0010: ena = 3'b010;
        4'b0100: ena = 3'b001;
        default: ena = 3'b000;
    endcase

// Johnson counter for incrementing digits
always @ (posedge clk, posedge sync_reset, posedge async_reset)
    if (async_reset) begin
        johnson <= 4'b0001;
        count <= 4'b0000;
        q <= 16'b0000000000000000; // Initialize all zeros
    end else if (sync_reset) begin
        johnson <= 4'b0001;
        count <= 4'b0000;
        q <= 16'b0000000000000000; // Initialize all zeros
    end else begin
        johnson <= {johnson[2:0], johnson[3]};
        case (johnson[3])
            1'b0: count <= count + 1;
            1'b1: count <= count;
        endcase
        q <= {bcd, bcd, bcd, bcd};
    end

endmodule