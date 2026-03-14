
module top_module (
clk,
up_down,
load,
reset,
A,
B,
EQ,
GT,
LT
);

// Declare the input/output ports
input clk;
input up_down;
input load;
input reset;
input [3:0] A;
input [3:0] B;
output wire EQ;
output wire GT;
output wire LT;

// Declare the internal register and wires
reg [3:0] counter;
wire [3:0] D;
wire [3:0] Q;

// Instantiate the up-down counter module
up_down_counter counter_module (
.clk(clk),
.up_down(up_down),
.load(load),
.reset(reset),
.D(D),
.Q(Q)
);

// Assign the value to D based on load signal
assign D = (load) ? A : Q; // if load is asserted, D takes the value of A, otherwise it takes the value of Q

// Instantiate the magnitude comparator module
magnitude_comparator comparator_module (
.A(Q), // Use the output of the counter as input to the comparator
.B(B),
.EQ(EQ),
.GT(GT),
.LT(LT)
);

endmodule

module up_down_counter (
clk,
up_down,
load,
reset,
D,
Q
);

// Declare the input/output ports
input clk;
input up_down;
input load;
input reset;
input [3:0] D;
output reg [3:0] Q;

// Implement the counter using always block
always @(posedge clk) begin
if (reset) begin
    Q <= 4'b0; // Reset the counter to 0
end else if (load) begin
    Q <= D; // Load the counter with the value of D
end else begin
    if (up_down) begin
        Q <= Q + 1; // Increment the counter if up_down is asserted
    end else begin
        Q <= Q - 1; // Decrement the counter if up_down is deasserted
    end
end
end

endmodule

module magnitude_comparator (
A,
B,
EQ,
GT,
LT
);

// Declare the input/output ports
input [3:0] A;
input [3:0] B;
output wire EQ;
output wire GT;
output wire LT;

// Implement the comparator using continuous assignment
assign EQ = (A == B);
assign GT = (A > B);
assign LT = (A < B);

endmodule
