module my_or_gate (
    X   ,
    A   ,
    B   ,
    C  
);

    output X   ;
    input  A   ;
    input  B   ;
    input  C   ;



   
    assign X = A | B | C;

endmodule