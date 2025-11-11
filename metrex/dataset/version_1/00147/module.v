module dff_sr (
    Q,
    Q_N,
    D,
    CLK,
    SET_B,
    RESET_B
);

    output Q;
    output Q_N;
    input  D;
    input  CLK;
    input  SET_B;
    input  RESET_B;

    reg Q;

    assign Q_N = ~Q;

    always @ (posedge CLK) begin
        if (!SET_B && !RESET_B) begin
            Q <= D;
        end else if (!SET_B) begin
            Q <= 1'b1;
        end else if (!RESET_B) begin
            Q <= 1'b0;
        end
    end

endmodule