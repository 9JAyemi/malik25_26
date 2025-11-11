
module altpcierd_tx_ecrc_ctl_fifo (
    aclr,
    clock,
    data,
    rdreq,
    wrreq,
    almost_full,
    empty,
    full,
    q);

    input aclr;
    input clock;
    input [0:0] data;
    input rdreq;
    input wrreq;
    output almost_full;
    output empty;
    output full;
    output [0:0] q;
    
    wire almost_empty;
    wire almost_full;
    
    reg q_reg = 1'b0;

    always @(posedge clock or posedge aclr)
        if (aclr)
            q_reg <= 1'b0;
        else if (!empty && rdreq)
            q_reg <= 1'bx;
        else if (wrreq && rdreq)
            q_reg <= 1'bx;
        else if (!full && wrreq)
            q_reg <= data;

    assign q = q_reg;
    assign full = 0;
    assign empty = q == 1'b0;
    assign almost_full = 0;

endmodule