
module mux4to1 (
    input A0,
    input A1,
    input A2,
    input A3,
    input S0,
    input S1,
    output X
);

    wire mux_2to1_0_out;
    wire mux_2to1_1_out;
    wire mux_2to1_2_out;

    mux2 mux_2to1_0 (mux_2to1_0_out, A0, A1, S0);
    mux2 mux_2to1_1 (mux_2to1_1_out, A2, A3, S0);
    mux2 mux_2to1_2 (mux_2to1_2_out, mux_2to1_0_out, mux_2to1_1_out, S1);

    mux2 mux_2to1_3 (X, mux_2to1_2_out, mux_2to1_2_out, S1);

endmodule

module mux2 (output out, input a, input b, input sel);
    assign out = sel ? b : a;
endmodule
