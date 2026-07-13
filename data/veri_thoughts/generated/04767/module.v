module sky130_fd_sc_hs__sedfxbp (
    input D,
    input DE,
    input SCD,
    input SCE,
    input VPWR,
    input VGND,
    output reg Q,
    output reg Q_N,
    input CLK
);

    always @(posedge CLK)
    begin
        if (SCD == 1'b0 && SCE == 1'b0 && DE == 1'b1 && VPWR == 1'b1 && VGND == 1'b0)
        begin
            if (D == 1'b1)
                Q <= 1'b1;
            else
                Q <= 1'b0;
        end
        else if (SCD == 1'b1 && SCE == 1'b1 && DE == 1'b0 && VPWR == 1'b0 && VGND == 1'b1)
        begin
            Q <= 1'b0;
        end
    end

    always @(posedge CLK)
    begin
        if (SCD == 1'b0 && SCE == 1'b0 && DE == 1'b1 && VPWR == 1'b1 && VGND == 1'b0)
        begin
            if (D == 1'b1)
                Q_N <= 1'b0;
            else
                Q_N <= 1'b1;
        end
        else if (SCD == 1'b1 && SCE == 1'b1 && DE == 1'b0 && VPWR == 1'b0 && VGND == 1'b1)
        begin
            Q_N <= 1'b1;
        end
    end

endmodule