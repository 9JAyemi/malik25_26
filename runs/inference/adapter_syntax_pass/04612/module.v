module logic_module (
    A,
    B,
    C,
    D,
    E,
    F,
    G,
    H,
    X
);

    input A;
    input B;
    input C;
    input D;
    input E;
    input F;
    input G;
    input H;
    output X;

    wire and0_out;
    wire or0_out;
    wire and1_out;
    wire or1_out;

    and and0 (and0_out, A, B);
    or or0 (or0_out, C, D);
    and and1 (and1_out, E, F);
    or or1 (or1_out, G, H);

    assign X = (and0_out || or0_out || !and1_out || !or1_out);

endmodule