module mux_2to1(
    input A, B, SEL,
    output Y);
    
    assign Y = SEL ? B : A;
    
endmodule