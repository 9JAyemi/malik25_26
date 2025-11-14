module mux2to1 (
    A   ,
    B   ,
    SEL ,
    OUT 
);

    input A   ;
    input B   ;
    input SEL ;
    output reg OUT ;

    always @(SEL or A or B)
    begin
        if (SEL == 0)
            OUT = A;
        else
            OUT = B;
    end

endmodule