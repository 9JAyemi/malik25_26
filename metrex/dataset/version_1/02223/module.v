
module ripple_adder(
    input [3:0] a,
    input [3:0] b,
    input clk,  // Added clock input
    output reg [4:0] sum
);

reg [3:0] a_reg, b_reg;
reg [3:0] carry_reg;

always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
end

always @(posedge clk) begin
    // Initialize the carry input for the first stage
    carry_reg[0] <= 0;

    sum[0] <= a_reg[0] ^ b_reg[0] ^ carry_reg[0];
    carry_reg[0] <= (a_reg[0] & b_reg[0]) | (a_reg[0] & carry_reg[0]) | (b_reg[0] & carry_reg[0]);
    sum[1] <= a_reg[1] ^ b_reg[1] ^ carry_reg[1];
    carry_reg[1] <= (a_reg[1] & b_reg[1]) | (a_reg[1] & carry_reg[1]) | (b_reg[1] & carry_reg[1]);
    sum[2] <= a_reg[2] ^ b_reg[2] ^ carry_reg[2];
    carry_reg[2] <= (a_reg[2] & b_reg[2]) | (a_reg[2] & carry_reg[2]) | (b_reg[2] & carry_reg[2]);
    sum[3] <= a_reg[3] ^ b_reg[3] ^ carry_reg[3];
    carry_reg[3] <= (a_reg[3] & b_reg[3]) | (a_reg[3] & carry_reg[3]) | (b_reg[3] & carry_reg[3]);
    sum[4] <= carry_reg[3];
end

endmodule
