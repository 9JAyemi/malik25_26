
module sky130_fd_sc_ms__a21boi_4 (
    Y,
    A1,
    A2,
    B1_N
);

    output Y;
    input A1;
    input A2;
    input B1_N;

    assign Y = (A1 & A2) | (~B1_N);

endmodule
