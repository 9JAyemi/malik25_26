module my_d_latch (
    input  D   ,
    output Q   ,
    input  GATE
);

reg Q;

always @(posedge GATE)
    Q <= D;

endmodule