module d_ff_reset (
    input D,
    input RESET_B,
    input CLK,
    output reg Q
);

    always @(posedge CLK or negedge RESET_B) begin
        if (!RESET_B) begin
            Q <= 0;
        end else begin
            Q <= D;
        end
    end

endmodule