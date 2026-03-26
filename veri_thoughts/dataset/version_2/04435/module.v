module d_ff_set_clr (
    input CLK,
    input D,
    input SET,
    input CLR,
    output reg Q
);

    always @(posedge CLK) begin
        if (SET) begin
            Q <= 1'b1;
        end else if (CLR) begin
            Q <= 1'b0;
        end else begin
            Q <= D;
        end
    end

endmodule