
module greater_of_two(
    input [7:0] A,
    input [7:0] B,
    output wire [7:0] G
);

    wire tmp;
    assign tmp = (A > B);
    assign G = tmp ? A : B;

endmodule
module comparator(
    input [7:0] A,
    input [7:0] B,
    output wire [7:0] G
);

    assign G = A > B ? A : B;

endmodule
module final_module(
    input [7:0] A,
    input [7:0] B,
    output wire [7:0] G
);

    wire [7:0] greater_output;
    wire [7:0] comparator_output;

    greater_of_two greater_inst(.A(A), .B(B), .G(greater_output));
    comparator comparator_inst(.A(A), .B(B), .G(comparator_output));

    assign G = comparator_output == A ? greater_output : B;

endmodule
module top_module (
    input [7:0] A,
    input [7:0] B,
    output wire [7:0] G
);

    final_module final_inst(.A(A), .B(B), .G(G));

endmodule