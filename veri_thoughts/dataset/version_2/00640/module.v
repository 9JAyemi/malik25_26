
module d_ff_as (
    input CLK,
    input D,
    input SET,
    input CLR,
    output Q,
    output Q_N
);

    reg Q_int;

    always @(posedge CLK ) begin  // or posedge SET) begin  // or posedge CLR removed
        if (SET) begin
            Q_int <= 1'b1;
        end else if (CLR) begin
            Q_int <= 1'b0;
        end else begin
            Q_int <= D;
        end
    end

    assign Q = Q_int;
    assign Q_N = ~Q_int;

endmodule
module top_module (
    input CLK,
    input D,
    input SET,
    input CLR,
    output Q,
    output Q_N
);

    d_ff_as d_ff (
        .CLK(CLK),
        .D(D),
        .SET(SET),
        .CLR(CLR),
        .Q(Q),
        .Q_N(Q_N)
    );

endmodule