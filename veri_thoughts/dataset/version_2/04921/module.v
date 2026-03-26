module flip_flop_async_reset_set (
    input D,
    input RESET_B,
    input SET_B,
    input CLK,
    output reg Q,
    output reg Q_B
);

    always @(posedge CLK) begin
        if (!RESET_B) begin
            Q <= 1'b0;
            Q_B <= 1'b1;
        end else if (!SET_B) begin
            Q <= 1'b1;
            Q_B <= 1'b0;
        end else begin
            Q <= D;
            Q_B <= ~D;
        end
    end

endmodule