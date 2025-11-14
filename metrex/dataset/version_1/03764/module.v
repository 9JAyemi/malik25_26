
module my_fifo (
    aclr,
    clock,
    data,
    rdreq,
    wrreq,
    q,
    usedw
);

    input aclr;
    input clock;
    input [33:0] data;
    input rdreq;
    input wrreq;
    output [33:0] q;
    output [9:0] usedw;

    wire [9:0] sub_wire0;
    wire [33:0] sub_wire1;

    scfifo scfifo_component (
        .aclr(aclr),
        .clock(clock),
        .data(data),
        .rdreq(rdreq),
        .wrreq(wrreq),
        .q(sub_wire1),
        .usedw(sub_wire0)
    );

    assign q = sub_wire1;
    assign usedw = sub_wire0;

endmodule
module scfifo (
    aclr,
    clock,
    data,
    rdreq,
    wrreq,
    q,
    usedw
);

    input aclr;
    input clock;
    input [33:0] data;
    input rdreq;
    input wrreq;
    output [33:0] q;
    output [9:0] usedw;

    reg [33:0] q_reg;
    reg [9:0] usedw_reg;

    assign q = q_reg;
    assign usedw = usedw_reg;

    always @(posedge clock or posedge aclr) begin
        if (aclr) begin
            q_reg <= 0;
            usedw_reg <= 0;
        end else begin
            if (wrreq) begin
                q_reg <= data;
                usedw_reg <= usedw_reg + 1;
            end

            if (rdreq) begin
                q_reg <= 0;
                usedw_reg <= usedw_reg - 1;
            end
        end
    end

endmodule