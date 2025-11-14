module four_to_one (
    Y ,
    A1,
    A2,
    B1,
    B2
);

    output Y ;
    input  A1;
    input  A2;
    input  B1;
    input  B2;
    
    assign Y = (A1 & A2) ? B1 : ((A1 ^ A2) ? B2 : (B1 & B2));

endmodule
