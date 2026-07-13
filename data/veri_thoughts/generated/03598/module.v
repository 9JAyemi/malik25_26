
module sky130_fd_sc_ls__a41oi (
    Y,
    A1,
    A2,
    A3,
    A4,
    B1
);

    // Module ports
    output Y ;
    input  A1;
    input  A2;
    input  A3;
    input  A4;
    input  B1;

    // Module logic
    assign Y = (A1 && A2) || (A3 && A4) || B1;

endmodule
