module min_shift_register (
    input [7:0] a, b, c, d, // Inputs for finding minimum value
    input clk, // Clock input for shift register
    output [7:0] min, // Output of the minimum value
    output q, // Output of the last flip-flop for shift register
    output [7:0] final_output // Final output of the system
);

// Find minimum value
wire [7:0] min_ab, min_cd, min_value;

// Compare a and b, c and d first
assign min_ab = (a < b) ? a : b;
assign min_cd = (c < d) ? c : d;

// Then find the minimum of min_ab and min_cd
assign min_value = (min_ab < min_cd) ? min_ab : min_cd;

assign min = min_value; // Assign the minimum value to min

// Shift register
reg [7:0] shift_reg;
always @(posedge clk) begin
    shift_reg <= min_value; // Load min_value into shift register on positive edge of clk
end

assign q = shift_reg[0]; // Assign the LSB of the shift register to q

// Final output
assign final_output = shift_reg; 

endmodule
