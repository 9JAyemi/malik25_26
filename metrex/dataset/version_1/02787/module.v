
module bit_counter (
    input [15:0] D,
    output [3:0] count,
    input clk // Added the clock input
);

// Create a 4-bit parallel prefix adder
wire [3:0] P[0:3];
assign P[0] = D[3:0];
assign P[1] = P[0] + D[7:4];
assign P[2] = P[1] + D[11:8];
assign P[3] = P[2] + D[15:12];

// Register the count
reg [3:0] count_reg;
always @(posedge clk) begin
    count_reg <= P[3]; // Corrected typo here
end

// Output the count
assign count = count_reg;

endmodule
