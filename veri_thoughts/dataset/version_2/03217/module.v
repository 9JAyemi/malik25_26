
module top_module (
    input clk,
    input reset,
    input signed [7:0] A,
    input signed [7:0] B,
    input signed [3:0] C,
    input select,
    output signed [3:0] D
);

    wire signed [15:0] prod;
    wire signed [15:0] sum;

    booth_multiplier booth_inst (
        .a(A),
        .b(B),
        .prod(prod)
    );

    adder adder_inst (
        .a(prod),
        .b(C),
        .sum(sum)
    );

    control_logic control_inst (
        .select(select),
        .sum(sum),
        .out(D)
    );

endmodule

module booth_multiplier (
    input signed [7:0] a,
    input signed [7:0] b,
    output signed [15:0] prod
);

    reg signed [7:0] A;
    reg signed [7:0] B;
    reg signed [15:0] P;

    always @(*) begin
        A = a;
        B = b;
        P = A * B;
    end

    assign prod = P;

endmodule

module adder (
    input signed [15:0] a,
    input signed [3:0] b,
    output signed [15:0] sum
);

    reg signed [15:0] A;
    reg signed [3:0] B;
    reg signed [15:0] S;

    always @(*) begin
        A = a;
        B = b;
        S = A + B;
    end

    assign sum = S;

endmodule

module control_logic (
    input select,
    input signed [15:0] sum,
    output reg signed [3:0] out
);

    always @(*) begin
        if (select == 0) begin
            out = sum[3:0];
        end else begin
            out = sum[7:4];
        end
    end

endmodule
