module d_ff_sync_reset_set_ce (
    input CLK,
    input D,
    input RESET,
    input SET,
    input CE,
    output reg Q
);

    always @(posedge CLK) begin
        if (CE) begin
            if (RESET) begin
                Q <= 0;
            end else if (SET) begin
                Q <= 1;
            end else begin
                Q <= D;
            end
        end
    end

endmodule