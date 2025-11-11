
module sequential_multiplier (
    input clk,
    input [7:0] A,
    input [7:0] B,
    output [15:0] P
);
    reg [15:0] temp_P;

    always @(posedge clk) begin
        temp_P <= A * B;
    end
    assign P = temp_P;
endmodule
module comparator (
    input [3:0] a,
    input [3:0] b,
    output reg eq,
    output reg gt_a,
    output reg gt_b
);

    always @(*) begin
        eq = (a == b);
        gt_a = (a > b);
        gt_b = (b > a);
    end

endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] A,
    input [7:0] B,
    input [3:0] a,
    input [3:0] b,
    output [15:0] P,
    output out
);
    wire eq, gt_a, gt_b;

    sequential_multiplier multiplier(
        .clk(clk),
        .A(A),
        .B(B),
        .P(P)
    );

    comparator comp(
        .a(a),
        .b(b),
        .eq(eq),
        .gt_a(gt_a),
        .gt_b(gt_b)
    );

    assign out = eq | gt_a;

endmodule