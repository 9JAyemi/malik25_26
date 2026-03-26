module dff_with_set(
    input D,
    input SET,
    input CLK,
    output reg Q
);

always @(posedge CLK) begin
    if (SET) begin
        Q <= 1;
    end else begin
        Q <= D;
    end
end

endmodule