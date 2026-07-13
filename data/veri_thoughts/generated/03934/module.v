
module add_sub (
    input [3:0] A,
    input [3:0] B,
    input SUB,
    output [3:0] result,
    output carry
);
    assign result = SUB ? A - B : A + B;
    assign carry = SUB ? A < B : 0;
endmodule
module multiplier (
    input [7:0] a,
    input [7:0] b,
    output [15:0] result
);
    assign result = a * b;
endmodule
module functional_module (
    input [3:0] add_sub_result,
    input [15:0] multiplier_result,
    input select,
    output [15:0] result
);
    assign result = select ? multiplier_result : {12'b0, add_sub_result};
endmodule
module top_module (
    input clk,
    input reset,
    input [3:0] A,
    input [3:0] B,
    input [7:0] a,
    input [7:0] b,
    input select,
    output [15:0] result
);
    wire [3:0] add_sub_result;
    wire carry;
    add_sub add_sub_inst (
        .A(A),
        .B(B),
        .SUB(select),
        .result(add_sub_result),
        .carry(carry)
    );
    wire [15:0] multiplier_result;
    multiplier multiplier_inst (
        .a(a),
        .b(b),
        .result(multiplier_result)
    );
    functional_module functional_inst (
        .add_sub_result(add_sub_result),
        .multiplier_result(multiplier_result),
        .select(select),
        .result(result)
    );
endmodule