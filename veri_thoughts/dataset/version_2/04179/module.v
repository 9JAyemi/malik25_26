
module sky130_fd_sc_hdll__isobufsrc (
    input A,
    output Z,
    input SLEEP
);

reg Z_reg; // Register to hold output value

assign Z = SLEEP ? 1'b0 : Z_reg;

always @(*) begin
    if (!SLEEP) begin
        Z_reg <= A; // Pass input to output
    end
end

endmodule