module mux_2to1 (
    out,
    in0,
    in1,
    sel
);

    output out;
    input in0;
    input in1;
    input sel;

    assign out = (sel == 1'b0) ? in0 : in1;

endmodule