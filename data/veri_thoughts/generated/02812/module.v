
module comparator (
    input [3:0] A,
    input [3:0] B,
    output reg EQ,
    output reg GT,
    output reg LT
);

always @* begin
    EQ = (A == B);
    GT = (A > B);
    LT = (A < B);
end

endmodule
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] A,    // Input to first comparator
    input [3:0] B,    // Input to first comparator
    output reg EQ1,   // Equal output of first comparator
    output reg GT1,   // Greater than output of first comparator
    output reg LT1,   // Less than output of first comparator
    input [3:0] C,    // Input to second comparator
    input [3:0] D,    // Input to second comparator
    output reg EQ2,   // Equal output of second comparator
    output reg GT2,   // Greater than output of second comparator
    output reg LT2,   // Less than output of second comparator
    output [3:0] q    // 4-bit output of the larger value
);

wire [3:0] larger_value;

comparator comp1(.A(A), .B(B), .EQ(EQ1), .GT(GT1), .LT(LT1));
comparator comp2(.A(C), .B(D), .EQ(EQ2), .GT(GT2), .LT(LT2));

assign larger_value = (GT1 || EQ1) ? A : B;
assign q = (GT2 || EQ2) ? (C > larger_value ? C : larger_value) : (D > larger_value ? D : larger_value);

endmodule