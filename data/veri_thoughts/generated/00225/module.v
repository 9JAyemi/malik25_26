
module top_module (
    input signed [3:0] A,
    input signed [3:0] B,
    output signed [3:0] out,
    output eq,
    output gt,
    output lt,
    output overflow
);

    wire signed [3:0] sum;
    wire overflow_adder;
    signed_comparator comp(A, B, eq, gt, lt);
    signed_adder adder(A, B, sum, overflow_adder);

    assign overflow = overflow_adder;

    assign out = (eq) ? sum : (gt) ? A : B;

endmodule

module signed_adder (
    input signed [3:0] A,
    input signed [3:0] B,
    output signed [3:0] out,
    output overflow
);

    wire [3:0] sum;
    wire carry;

    assign overflow = (A[3] == B[3] && sum[3] != A[3]) ? 1 : 0;

    assign {carry, sum} = A + B;

    assign out = {overflow, sum};

endmodule

module signed_comparator (
    input signed [3:0] A,
    input signed [3:0] B,
    output eq,
    output gt,
    output lt
);

    assign eq = (A == B);

    assign gt = (A > B);

    assign lt = (A < B);

endmodule
