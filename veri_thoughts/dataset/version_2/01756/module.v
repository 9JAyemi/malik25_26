module d_flip_flop_async_reset (
    output reg Q,
    input CLK,
    input D,
    input RESET_B
);

    always @(posedge CLK, negedge RESET_B) begin
        if (!RESET_B) begin
            Q <= 0;
        end else begin
            Q <= D;
        end
    end

endmodule