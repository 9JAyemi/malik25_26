module d_ff_with_async_reset_set (
    input D,
    input CLK,
    input SCD,
    input SCE,
    output Q,
    output Q_N
);

    reg Q;
    reg Q_N;

    always @(posedge CLK) begin
        if (SCD) begin
            Q <= 0;
            Q_N <= 1;
        end
        else if (SCE) begin
            Q <= 1;
            Q_N <= 0;
        end
        else begin
            Q <= D;
            Q_N <= ~D;
        end
    end

endmodule