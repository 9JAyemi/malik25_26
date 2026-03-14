module dff (
    input CLK,
    input D,
    input SCD,
    input SCE,
    input SET_B,
    output reg Q
);

    always @(posedge CLK) begin
        if (SCD) begin
            if (SCE) begin
                Q <= D;
            end
            else begin
                Q <= 1'b0;
            end
        end
        else begin
            if (SET_B) begin
                Q <= 1'b1;
            end
            else begin
                Q <= Q;
            end
        end
    end

endmodule

module dff_srst_as_set (
    input CLK,
    input D,
    input S,
    input R,
    output Q
);

    wire Q_bar;
    wire SCD;
    wire SCE;
    wire SET_B;

    assign SCD = R;
    assign SCE = 1;
    assign SET_B = S;

    dff base (
        .Q(Q),
        .CLK(CLK),
        .D(D),
        .SCD(SCD),
        .SCE(SCE),
        .SET_B(SET_B)
    );

endmodule