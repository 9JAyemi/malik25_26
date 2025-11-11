module dff_async_reset_enable (
    input CLK,
    input D,
    input RESET,
    input EN,
    output Q,
    output Q_N
);

reg Q;
reg Q_N;

always @(posedge CLK or negedge RESET)
begin
    if (!RESET)
    begin
        Q <= 1'b0;
        Q_N <= 1'b1;
    end
    else if (!EN)
    begin
        Q <= Q;
        Q_N <= Q_N;
    end
    else
    begin
        Q <= D;
        Q_N <= ~D;
    end
end

endmodule