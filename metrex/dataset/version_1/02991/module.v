module pipelined_ripple_carry_adder_4bit (
    input clk,                // Correct position for the clock input
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output reg [3:0] Sum,
    output reg Cout
);

reg [3:0] A_reg, B_reg;
reg Cin_reg, Cout_reg1, Cout_reg2, Cout_reg3; // Use separate registers for each carry-out

// Pipeline stage 1
always @(posedge clk) begin
    A_reg <= A;
    B_reg <= B;
    Cin_reg <= Cin;
end

// Pipeline stage 2
always @(posedge clk) begin
    // Full adder for bit 0
    {Cout_reg1, Sum[0]} = A_reg[0] + B_reg[0] + Cin_reg;
    
    // Full adder for bit 1
    {Cout_reg2, Sum[1]} = A_reg[1] + B_reg[1] + Cout_reg1;
    
    // Full adder for bit 2
    {Cout_reg3, Sum[2]} = A_reg[2] + B_reg[2] + Cout_reg2;
    
    // Full adder for bit 3
    {Cout, Sum[3]} = A_reg[3] + B_reg[3] + Cout_reg3;
end


endmodule
