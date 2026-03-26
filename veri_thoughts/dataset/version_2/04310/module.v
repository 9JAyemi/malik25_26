module d_latch_with_reset_and_enable (
    input clk,
    input D,
    input EN,
    input RESET,
    output reg Q,
    output reg Q_n
);

    always @(posedge clk) begin
        if (RESET) begin
            Q <= 1'b0;
            Q_n <= 1'b1;
        end else if (EN) begin
            Q <= D;
            Q_n <= ~D;
        end
    end

endmodule