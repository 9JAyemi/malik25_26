
module top_module (
    input [7:0] in,
    input clk,
    output reg [8:0] out
);

    // Odd parity bit generator
    reg [7:0] data_in;
    reg parity;
    
    always @(posedge clk) begin
        data_in <= in;
        parity <= ~(^data_in); // Calculate the parity bit
    end

    // Priority encoder
    wire [2:0] position;
    assign position = (in == 8'b00000000) ? 3'b000 :
                      (in == 8'b00000001) ? 3'b001 :
                      (in == 8'b00000010) ? 3'b010 :
                      (in == 8'b00000100) ? 3'b011 :
                      (in == 8'b00001000) ? 3'b100 :
                      (in == 8'b00010000) ? 3'b101 :
                      (in == 8'b00100000) ? 3'b110 :
                      (in == 8'b01000000) ? 3'b111 : 3'bxxx; // Handle the case when input is not a valid 8-bit number

    // Final output
    always @(posedge clk) begin
        out[8] <= parity; // Assign the parity bit
        out[7:5] <= position; // Assign the position of the first '1' bit
        out[4:0] <= 5'b0; // Zero-pad the rest of the output
    end

endmodule