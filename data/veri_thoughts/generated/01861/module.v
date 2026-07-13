module top_module (
    X   ,
    A1  ,
    A2  ,
    A3  ,
    B1  ,
    C1 
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  A3  ;
    input  B1  ;
    input  C1  ;

    
    assign X = (A1 | A2 |A3) & B1 & C1;

   
    
endmodule