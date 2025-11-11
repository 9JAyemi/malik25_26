module sky130_fd_sc_ms__dlxtn (
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    input GATE_N,
    output reg Q
);

always @ (GATE_N, VPWR, VGND, VPB, VNB, D)
begin
    if (GATE_N == 1'b0) begin
        Q <= 1'bx;
    end else begin
        if (VPWR == 1'b1 && VGND == 1'b0) begin
            Q <= D;
        end else if (VPWR == 1'b0 && VGND == 1'b0) begin
            Q <= VPB;
        end else if (VPWR == 1'b1 && VGND == 1'b1) begin
            Q <= VNB;
        end else if (VPWR == 1'b0 && VGND == 1'b1) begin
            Q <= VGND;
        end
    end
end

endmodule