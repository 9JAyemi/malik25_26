module d_ff_scd_sce (
    input CLK,
    input D,
    input SCD,
    input SCE,
    output reg Q,
    output reg Q_N
);

    always @(posedge CLK) begin
        if (SCD) begin
            Q <= 0;
            Q_N <= 1;
        end else if (SCE) begin
            Q <= D;
            Q_N <= ~D;
        end
    end

endmodule