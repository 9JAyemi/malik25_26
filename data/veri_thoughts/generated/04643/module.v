
module or4bb (
    input A,
    input B,
    input C_N,
    input D_N,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output reg X
);

    always @(*) begin
        X = A | B | ~C_N | ~D_N | VPWR | VGND | VPB | VNB;
    end

endmodule

