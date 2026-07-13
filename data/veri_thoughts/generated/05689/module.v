module sky130_fd_sc_hs__mux2i (
    input A0,
    input A1,
    input S,
    input VPWR,
    input VGND,
    output reg Y
);

always @(*) begin
    if (S == 1'b0) begin
        Y = A0;
    end else if (S == 1'b1) begin
        Y = A1;
    end else begin
        Y = 1'bx;
    end
end

endmodule