
module mux_4to1 (
    Y,
    D0,
    D1,
    D2,
    D3,
    SEL,
    EN
);

    // Module ports
    output Y;
    input  D0;
    input  D1;
    input  D2;
    input  D3;
    input  [1:0] SEL;
    input  EN;

    // Local signals
    wire mux_2to1_out_0;
    wire mux_2to1_out_1;
    wire mux_2to1_out_2;

    // Instantiate 2-to-1 multiplexers
    mux_2to1 u_mux_0 (mux_2to1_out_0, D0, D1, SEL[0]);
    mux_2to1 u_mux_1 (mux_2to1_out_1, D2, D3, SEL[0]);
    mux_2to1 u_mux_2 (mux_2to1_out_2, mux_2to1_out_0, mux_2to1_out_1, SEL[1]);

    // Output buffer
    bufif0 u_buf (Y, mux_2to1_out_2, EN);

endmodule
module mux_2to1 (
    Y,
    A,
    B,
    S
);

    // Module ports
    output Y;
    input  A;
    input  B;
    input  S;

    // Local signals
    wire not_S;
    wire and_0;
    wire and_1;

    // Logic gates
    not u_not_gate (not_S, S);
    and u_and_gate_0 (and_0, A, not_S);
    and u_and_gate_1 (and_1, B, S);

    // Output buffer
    buf u_buf (Y, and_0, and_1);

endmodule