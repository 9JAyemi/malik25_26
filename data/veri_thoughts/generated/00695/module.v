module edge_detector (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

reg [7:0] prev_in;
reg [7:0] edge_detected;

parameter IDLE = 2'b00;
parameter RISING_EDGE = 2'b01;
parameter FALLING_EDGE = 2'b10;

always @(posedge clk) begin
    case (prev_in ^ in)
        8'b00000001, 8'b00000010, 8'b00000100, 8'b00001000, 8'b00010000, 8'b00100000, 8'b01000000, 8'b10000000:
            edge_detected <= RISING_EDGE;
        8'b11111110, 8'b11111101, 8'b11111011, 8'b11110111, 8'b11101111, 8'b11011111, 8'b10111111, 8'b01111111:
            edge_detected <= FALLING_EDGE;
        default:
            edge_detected <= IDLE;
    endcase
    prev_in <= in;
end

assign anyedge = edge_detected;

endmodule