module mux2to1 (
    input a,
    input b,
    input sel,
    output y
);

    assign y = (sel == 0) ? a : b;

endmodule