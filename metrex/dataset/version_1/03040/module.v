
module dff_asr (
    input  D,
    input  CLK,
    input  SET_B,
    input  RESET_B,
    output Q,
    output Q_N
);

    reg  Q;
    assign Q_N = ~Q;

    always @(posedge CLK) begin
        if (!SET_B) begin
            Q <= 1'b1;
        end else if (!RESET_B) begin
            Q <= 1'b0;
        end else begin
            Q <= D;
        end
    end

endmodule