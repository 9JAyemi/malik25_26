module and4b (
    input  A_N,
    input  B  ,
    input  C  ,
    input  D  ,
    output X
);

    assign X = ~(A_N | B | C | D);

endmodule