module flip_flop (
    Q,
    CLK,
    D,
    SCD,
    SCE,
    RESET_B
);

    output Q;
    input CLK;
    input D;
    input SCD;
    input SCE;
    input RESET_B;

    reg Q;

    always @(posedge CLK or negedge RESET_B) begin
        if (!RESET_B) begin
            Q <= 0;
        end else if (SCD) begin
            Q <= 1;
        end else if (SCE) begin
            Q <= 0;
        end else begin
            Q <= D;
        end
    end

endmodule