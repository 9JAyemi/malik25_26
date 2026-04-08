
module top_module (
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] SUM,
    output COUT,
    output LT
);

    wire [3:0] adder_sum;
    wire adder_cout;
    wire lt;

    ripple_carry_adder adder(.A(A), .B(B), .CIN(CIN), .SUM(adder_sum), .COUT(adder_cout));
    magnitude_comparator comparator(.A(A), .B(B), .LT(lt));

    assign SUM = adder_sum;
    assign COUT = adder_cout;
    assign LT = lt;

endmodule
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] SUM,
    output COUT
);

    wire [3:0] fa1_sum;
    wire fa1_cout;
    wire [3:0] fa2_sum;
    wire fa2_cout;
    wire [3:0] fa3_sum;
    wire fa3_cout;
    wire [3:0] fa4_sum;

    full_adder fa1(.A(A[0]), .B(B[0]), .CIN(CIN), .SUM(fa1_sum[0]), .COUT(fa1_cout));
    full_adder fa2(.A(A[1]), .B(B[1]), .CIN(fa1_cout), .SUM(fa2_sum[1]), .COUT(fa2_cout));
    full_adder fa3(.A(A[2]), .B(B[2]), .CIN(fa2_cout), .SUM(fa3_sum[2]), .COUT(fa3_cout));
    full_adder fa4(.A(A[3]), .B(B[3]), .CIN(fa3_cout), .SUM(fa4_sum[3]), .COUT(COUT));

    assign SUM = {fa4_sum[3], fa3_sum[2], fa2_sum[1], fa1_sum[0]};

endmodule
module full_adder (
    input A,
    input B,
    input CIN,
    output SUM,
    output COUT
);

    assign SUM = A ^ B ^ CIN;
    assign COUT = (A & B) | (A & CIN) | (B & CIN);

endmodule
module magnitude_comparator (
    input [3:0] A,
    input [3:0] B,
    output LT
);

    assign LT = (A < B);

endmodule