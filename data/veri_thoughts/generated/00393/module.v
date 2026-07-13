
module counter_with_reset (
    input clk,
    input reset,      // Synchronous active-high reset
    output reg [3:0] count_out // 4-bit output from the counter after reaching maximum value
);

always @(posedge clk) begin
    if (reset) begin
        count_out <= 4'b0; // Reset the counter to 0
    end else begin
        if (count_out == 4'b1111) begin
            count_out <= 4'b0; // Reset the counter to 0 when it reaches maximum value
        end else begin
            count_out <= count_out + 1; // Increment the counter
        end
    end
end

endmodule

module barrel_shifter (
    input [15:0] data_in, // 16-bit input for the barrel shifter
    input [3:0] shift_amt, // 4-bit shift amount for the barrel shifter
    output [15:0] data_out // 16-bit output from the barrel shifter
);

assign data_out = (shift_amt == 4'b0000) ? data_in : // No shift
                 (shift_amt == 4'b0001) ? {data_in[14:0], 1'b0} : // Shift left by 1 bit
                 (shift_amt == 4'b0010) ? {data_in[13:0], 2'b00} : // Shift left by 2 bits
                 (shift_amt == 4'b0011) ? {data_in[12:0], 3'b000} : // Shift left by 3 bits
                 (shift_amt == 4'b0100) ? {data_in[11:0], 4'b0000} : // Shift left by 4 bits
                 (shift_amt == 4'b0101) ? {data_in[10:0], 5'b00000} : // Shift left by 5 bits
                 (shift_amt == 4'b0110) ? {data_in[9:0], 6'b000000} : // Shift left by 6 bits
                 (shift_amt == 4'b0111) ? {data_in[8:0], 7'b0000000} : // Shift left by 7 bits
                 (shift_amt == 4'b1000) ? {data_in[7:0], 8'b00000000} : // Shift left by 8 bits
                 (shift_amt == 4'b1001) ? {data_in[6:0], 9'b000000000} : // Shift left by 9 bits
                 (shift_amt == 4'b1010) ? {data_in[5:0], 10'b0000000000} : // Shift left by 10 bits
                 (shift_amt == 4'b1011) ? {data_in[4:0], 11'b00000000000} : // Shift left by 11 bits
                 (shift_amt == 4'b1100) ? {data_in[3:0], 12'b000000000000} : // Shift left by 12 bits
                 (shift_amt == 4'b1101) ? {data_in[2:0], 13'b0000000000000} : // Shift left by 13 bits
                 (shift_amt == 4'b1110) ? {data_in[1:0], 14'b00000000000000} : // Shift left by 14 bits
                 (shift_amt == 4'b1111) ? {data_in[0], 15'b000000000000000} : // Shift left by 15 bits
                 16'b0; // Default case

endmodule

module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [15:0] data_in, // 16-bit input for the barrel shifter
    input [3:0] shift_amt, // 4-bit shift amount for the barrel shifter,
    output [3:0] count_out // 4-bit output from the counter after reaching maximum value
);

wire [15:0] shifted_data;
barrel_shifter barrel_shifter_inst (
    .data_in(data_in),
    .shift_amt(shift_amt),
    .data_out(shifted_data)
);

counter_with_reset counter_with_reset_inst (
    .clk(clk),
    .reset(reset),
    .count_out(count_out)
);

endmodule
