
module decoder_3to8 (
    input A,
    input B,
    input C,
    output Y0,
    output Y1,
    output Y2,
    output Y3,
    output Y4,
    output Y5,
    output Y6,
    output Y7
);

reg [2:0] input_reg;
wire [7:0] output_wire;

assign output_wire = (input_reg == 3'b000) ? 8'b00000001 :
                     (input_reg == 3'b001) ? 8'b00000010 :
                     (input_reg == 3'b010) ? 8'b00000100 :
                     (input_reg == 3'b011) ? 8'b00001000 :
                     (input_reg == 3'b100) ? 8'b00010000 :
                     (input_reg == 3'b101) ? 8'b00100000 :
                     (input_reg == 3'b110) ? 8'b01000000 :
                                           8'b10000000 ;

always @(A or B or C) begin
    input_reg <= {C, B, A};
end

assign {Y7, Y6, Y5, Y4, Y3, Y2, Y1, Y0} = output_wire;

endmodule
