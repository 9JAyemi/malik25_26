
module generate_Z (
    input A1,
    input A2,
    input B1,
    input B2,
    input C1,
    output reg [1:0] Z
);

    wire Y;
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;
    
    assign Y = (A1 & B2 & C1) | (A2 & B1 & C1) | (A1 & B1 & ~C1) | (A2 & B2 & ~C1);
    always @ (Y) begin
        case (Y)
            2'b00: Z = 2'b00;
            2'b01: Z = 2'b01;
            2'b10: Z = 2'b10;
            2'b11: Z = 2'b11;
        endcase
    end

endmodule