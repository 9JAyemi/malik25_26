module mux2to1 (
    // inputs
    input  sel,
    input  in0,
    input  in1,
    // outputs
    output out
);

    assign out = sel ? in1 : in0;

endmodule