
module mux2to1 (o, a, b, sel);
    output o;
    input a, b, sel;
    assign o = sel ? b : a;
endmodule