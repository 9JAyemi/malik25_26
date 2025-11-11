
module BitsliceALU (
    input  [15:0] A,
    input  [15:0] B,
    input  [5:0] Op,
    output [15:0] Q,
    output [2:0] Flags
);

    wire [15:0] result;
    wire [3:0] X, Y;
    wire [4:0] C;
    wire [3:0] Z;
    wire [3:0] C_out;

    Circuit74181b slice3 (
        .a(A[15:12]),
        .b(B[15:12]),
        .c(Op[4:1]),
        .d(C[2]),
        .e(Op[5]),
        .f(1'b0),
        .g(result[15:12]),
        .h(X[3]),
        .i(Y[3]),
        .j(C[3])
    );
    Circuit74181b slice2 (
        .a(A[11:8]),
        .b(B[11:8]),
        .c(Op[4:1]),
        .d(C[1]),
        .e(Op[5]),
        .f(1'b0),
        .g(result[11:8]),
        .h(X[2]),
        .i(Y[2]),
        .j(C[2])
    );
    Circuit74181b slice1 (
        .a(A[7:4]),
        .b(B[7:4]),
        .c(Op[4:1]),
        .d(C[0]),
        .e(Op[5]),
        .f(1'b0),
        .g(result[7:4]),
        .h(X[1]),
        .i(Y[1]),
        .j(C[1])
    );
    Circuit74181b slice0 (
        .a(A[3:0]),
        .b(B[3:0]),
        .c(Op[4:1]),
        .d(Op[5]),
        .e(Op[0]),
        .f(1'b0),
        .g(result[3:0]),
        .h(X[0]),
        .i(Y[0]),
        .j(C[0])
    );

    assign Q = result;

    assign Flags[0] = ~C_out[3];
    assign Flags[1] = result[15];
    assign Flags[2] = (result == 16'h0000);

    assign C_out[0] = C[0];
    assign C_out[1] = C[1] | (C[0] & ~Y[1]);
    assign C_out[2] = C[2] | (C[1] & ~Y[2]) | (C[0] & ~Y[1] & ~Y[2]);
    assign C_out[3] = C[3] | (C[2] & ~Y[3]) | (C[1] & ~Y[2] & ~Y[3]) | (C[0] & ~Y[1] & ~Y[2] & ~Y[3]);
endmodule
module Circuit74181b (
    input [3:0] a,
    input [3:0] b,
    input [3:0] c,
    input d,
    input e,
    input [1:0] f,
    output [3:0] g,
    output h,
    output i,
    output j
);
    wire [3:0] P, G;

    assign P[0] = a[0] & b[0];
    assign P[1] = a[1] & b[1];
    assign P[2] = a[2] & b[2];
    assign P[3] = a[3] & b[3];

    assign G[0] = a[0] | b[0];
    assign G[1] = a[1] | b[1];
    assign G[2] = a[2] | b[2];
    assign G[3] = a[3] | b[3];

    assign g[0] = P[0];
    assign g[1] = P[1] | (P[0] & G[1]);
    assign g[2] = P[2] | (P[1] & G[2]) | (P[0] & G[1] & G[2]);
    assign g[3] = P[3] | (P[2] & G[3]) | (P[1] & G[2] & G[3]) | (P[0] & G[1] & G[2] & G[3]);

    assign h = c[0];
    assign i = e & f[0];
    assign j = ~e | ~f[1];
endmodule