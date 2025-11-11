module d_ff_async_reset (
    input D,
    input RESET_B,
    input CLK,
    output Q,
    output Q_N
);

    reg q;
    assign Q = q;
    assign Q_N = ~q;

    always @(posedge CLK or negedge RESET_B) begin
        if (~RESET_B) begin
            q <= 0;
        end else begin
            q <= D;
        end
    end

endmodule