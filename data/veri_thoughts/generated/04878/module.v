module d_flip_flop (
    input D,
    input CLK,
    input RESET,
    output Q
);

    reg Q_reg;

    always @(posedge CLK) begin
        if (RESET) begin
            Q_reg <= 1'b0;
        end else begin
            Q_reg <= D;
        end
    end

    assign Q = Q_reg;

endmodule