
module mux (
    input A,
    input B,
    input C,
    input invert,
    output out
);

reg out_reg;

always @ * begin
    if (C == 1'b0) begin
        out_reg <= A;
    end else if (C == 1'b1) begin
        if (invert == 1'b0) begin
            out_reg <= B;
        end else begin
            out_reg <= ~B;
        end
    end
end

assign out = out_reg;

endmodule