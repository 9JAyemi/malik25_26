module mux_2to1 (
    output reg out,
    input in0,
    input in1,
    input sel
);

always @(*) begin
    if (sel == 0) begin
        out = in0;
    end else begin
        out = in1;
    end
end

endmodule