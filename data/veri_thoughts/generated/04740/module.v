
module sky130_fd_sc_lp__o21ai (
    input A1,
    input A2,
    input B1,
    output Y,
    input VDD,
    input VSS
);

    wire a1_in;
    wire a2_in;
    wire b1_in;
    wire y_out;

    not (a1_in, A1);
    not (a2_in, A2);
    not (b1_in, B1);

    nand (y_out, a1_in, a2_in);

    or (Y, y_out, b1_in);

endmodule
