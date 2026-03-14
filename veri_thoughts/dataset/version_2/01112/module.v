
module my_4input_nand (
    Y   ,
    A   ,
    B   ,
    C   ,
    D   
);

    output Y   ;
    input  A   ;
    input  B   ;
    input  C   ;
    input  D   ;
    
    wire nand1_out;
    wire nand2_out;
    wire nand3_out;
    
    nand (
        nand1_out,
        A,
        B,
        C,
        D
    );
    
    nand (
        nand2_out,
        nand1_out,
        nand1_out
    );
    
    not (
        nand3_out,
        nand2_out
    );
    
    assign Y = nand3_out;

endmodule
