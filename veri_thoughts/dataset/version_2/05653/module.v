module d_ff_res (
    output reg Q,
    input D,
    input CLK,
    input RESET
);

    reg Q_next;

    always @ (posedge CLK or negedge RESET) begin
        if (!RESET) begin
            Q <= 0;
        end else begin
            Q <= Q_next;
        end
    end

    always @ (D, RESET) begin
        if (!RESET) begin
            Q_next <= 0;
        end else begin
            Q_next <= D;
        end
    end

endmodule