module four_in_one_out (
    X ,
    A1,
    A2,
    A3,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;


    assign X = ((A1 & A2) | (A3 & B1)) ? 1'b1 : 1'b0;

endmodule