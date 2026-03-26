module light_ctrl(
    output X,
    input A1,
    input A2,
    input A3,
    input B1
);

    wire or0_out;
    wire or1_out;
    wire or2_out;
    wire and0_out;
    wire and1_out;
    wire and2_out;
    wire and3_out;

    or or0(or0_out, A1, A2);
    or or1(or1_out, A2, A3);
    or or2(or2_out, A1, A3);
    and and0(and0_out, or0_out, or1_out);
    and and1(and1_out, or0_out, or2_out);
    and and2(and2_out, or1_out, or2_out);
    and and3(and3_out, and0_out, and1_out, and2_out, B1);

    assign X = and3_out;

endmodule