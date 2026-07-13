module three_input_and (
    input  VPWR,
    input  VGND,
    input  a   ,
    input  b   ,
    input  c   ,
    output out
);

    // Local signals
    wire   and0_out        ;
    wire   and1_out        ;
    wire   u_vpwr_vgnd0_out;

    // Instantiate gates
    and and0 (and0_out, a, b);
    and and1 (and1_out, and0_out, c);
    not not0 (out, and1_out);

endmodule