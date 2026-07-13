
module d_ff_sync_reset (
    input CLK,
    input D,
    input RESET,
    output Q,
    output Q_N
);

    reg Q_buf;

    always @(posedge CLK) begin
        if (RESET) begin
            Q_buf <= 1'b0;
        end
        else begin
            Q_buf <= D;
        end
    end

    assign Q = Q_buf;
    assign Q_N = ~Q_buf;

endmodule
