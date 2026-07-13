module power_module (
    input VPB,
    input VPWR,
    input VGND,
    input VNB,
    output reg HI,
    output reg LO
);

always @* begin
    if (VPB) begin
        HI = 1;
        LO = 0;
    end else if (VPWR && !VGND) begin
        HI = 1;
        LO = 0;
    end else if (VNB) begin
        HI = 0;
        LO = 1;
    end else if (!VPWR && VGND) begin
        HI = 0;
        LO = 1;
    end else begin
        HI = 0;
        LO = 0;
    end
end

endmodule