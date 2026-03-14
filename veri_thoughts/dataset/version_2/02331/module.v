module mux_2to1 (
    input A,
    input B,
    input sel,
    output out
);

    assign out = (sel == 1'b0) ? A : B;

endmodule