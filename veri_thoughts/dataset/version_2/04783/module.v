module logical_operation (
    Y ,
    A1,
    A2,
    B1,
    C1,
    D1
);

    output Y ;
    input  A1;
    input  A2;
    input  B1;
    input  C1;
    input  D1;

    assign Y = (A1 & A2) ? 1 :
               (A1 & !A2) ? B1 :
               (!A1 & A2) ? C1 :
               (!A1 & !A2 & !B1 & !C1) ? D1 :
               0;

endmodule