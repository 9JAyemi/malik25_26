module flip_flop(
    input D,
    input SET,
    input SLEEP_B,
    input KAPWR,
    input VGND,
    input VPWR,
    output reg Q,
    input CLK
);

    always @(posedge CLK) begin
        if (SET) begin
            Q <= 1'b1;
        end else if (SLEEP_B) begin
            Q <= 1'b0;
        end else begin
            Q <= D;
        end
    end

endmodule