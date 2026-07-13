
module d_flip_flop (
    input D,
    input CLK,
    input RESET,
    input SET,
    output reg Q
);

always @(posedge CLK or negedge RESET) begin
    if (!RESET) begin
        Q <= 1'b0;
    end else if (SET) begin
        Q <= 1'b1;
    end else begin
        Q <= D;
    end
end

endmodule