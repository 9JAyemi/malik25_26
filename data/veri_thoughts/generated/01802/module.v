module d_ff_set_clear (
    input D,
    input CLK,
    input SET_B,
    input SCD,
    output reg Q
);

    always @(posedge CLK) begin
        if (SET_B == 0) begin
            Q <= 1;
        end else if (SCD == 0) begin
            Q <= 0;
        end else begin
            Q <= D;
        end
    end

endmodule