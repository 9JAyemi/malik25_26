
module full_adder_1bit(
    input A,
    input B,
    input CIN,
    output SUM,
    output COUT
);

    assign SUM = A ^ B ^ CIN;
    assign COUT = (A & B) | (B & CIN) | (A & CIN);

endmodule
module adder_subtractor_4bit(
    input [3:0] A,
    input [3:0] B,
    input SEL,
    input CLK,
    input RST,
    output [3:0] Y,
    output COUT
);

    wire [3:0] sum;
    wire [3:0] neg_b;
    wire [3:0] twos_comp_b;

    full_adder_1bit fa0(.A(A[0]), .B(neg_b[0]), .CIN(SEL), .SUM(sum[0]));
    full_adder_1bit fa1(.A(A[1]), .B(neg_b[1]), .CIN(sum[0]), .SUM(sum[1]));
    full_adder_1bit fa2(.A(A[2]), .B(neg_b[2]), .CIN(sum[1]), .SUM(sum[2]));
    full_adder_1bit fa3(.A(A[3]), .B(neg_b[3]), .CIN(sum[2]), .SUM(sum[3]), .COUT(COUT));

    assign neg_b = ~B + 1;
    assign twos_comp_b = SEL ? B : neg_b;
    assign Y = SEL ? sum : twos_comp_b;

endmodule