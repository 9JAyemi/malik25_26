module bridge (
    input [7:0] RGA,
    input [0:0] RGB,
    input [7:0] OPT,
    input [1:0] KEY,
    input CLK,
    input RST,
    input ENA,
    output reg [7:0] RGZ
);

reg [7:0] shift_reg;
reg [7:0] not_reg;
reg [7:0] zero_reg;

always @ (posedge CLK or negedge RST)
begin
    if (!RST)
    begin
        shift_reg <= 8'b0;
        not_reg <= 8'b0;
        zero_reg <= 8'b0;
    end
    else if (ENA)
    begin
        case ({OPT, KEY})
            8'b00000010: shift_reg <= {RGA[6:0], 1'b0};
            8'b00000000: shift_reg <= {1'b0, RGA[7:1]};
            8'b00000011: shift_reg <= {RGA[5:0], 2'b00};
            8'b00000001: shift_reg <= {2'b00, RGA[7:2]};
            8'b00000100: not_reg <= ~RGA;
            8'b00000010: zero_reg <= 8'b0;
            default: shift_reg <= RGA;
        endcase
    end
end

always @*
begin
    RGZ = RGB ? not_reg : (KEY == 2'b10 ? zero_reg : shift_reg);
end

endmodule