
module mux2_1(
    input A,
    input B,
    input SEL,
    output VOUT,
    output VOUT_N
);
    assign VOUT = (SEL)? B:A;
    assign VOUT_N = ~(SEL)? B:A;

endmodule