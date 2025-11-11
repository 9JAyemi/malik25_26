
module shift_register (
    LOAD,
    DATA_IN,
    CLK,
    RESET_B,
    DATA_OUT,
    Q_N
);

    input LOAD;
    input [3:0] DATA_IN;
    input CLK;
    input RESET_B;
    output [3:0] DATA_OUT;
    output Q_N;

    wire [3:0] Q;
    wire DATAPATH_LOAD;

    assign DATAPATH_LOAD = RESET_B && LOAD;

    DFF flip_flop_0 (
        .D(DATA_IN[0]),
        .Q(Q[0]),
        .CLK(CLK),
        .RST_N(RESET_B),
        .SET_N(DATAPATH_LOAD)
    );

    DFF flip_flop_1 (
        .D(Q[0]),
        .Q(Q[1]),
        .CLK(CLK),
        .RST_N(RESET_B),
        .SET_N(DATAPATH_LOAD)
    );

    DFF flip_flop_2 (
        .D(Q[1]),
        .Q(Q[2]),
        .CLK(CLK),
        .RST_N(RESET_B),
        .SET_N(DATAPATH_LOAD)
    );

    DFF flip_flop_3 (
        .D(Q[2]),
        .Q(Q[3]),
        .CLK(CLK),
        .RST_N(RESET_B),
        .SET_N(DATAPATH_LOAD)
    );

    assign Q_N = ~Q[3];

    assign DATA_OUT = Q;

endmodule
module DFF (
    D,
    Q,
    CLK,
    RST_N,
    SET_N
);

    input D;
    output Q;
    input CLK;
    input RST_N;
    input SET_N;

    wire D1, D2;

    nand (D1, RST_N, SET_N);
    nand (D2, D1, D, CLK);
    nand (Q, RST_N, CLK, D2);

endmodule