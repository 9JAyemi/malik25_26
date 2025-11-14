module d_latch (
    input D,
    input S,
    input R,
    input CLK,
    output Q
);

reg Q;

always @(posedge CLK) begin
    if (R) begin
        Q <= 0;
    end else if (S) begin
        Q <= 1;
    end else begin
        Q <= D;
    end
end

endmodule