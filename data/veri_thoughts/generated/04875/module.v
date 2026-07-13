
module decoder_8to64 (
    input [7:0] ABCDEFGH,
    output reg [63:0] Y
);

reg [5:0] stage;
reg [63:0] Y_reg;

always @(*) begin
    case(stage)
        6'b000001: Y_reg = 64'b00000001;
        6'b000010: Y_reg = 64'b00000010;
        6'b000100: Y_reg = 64'b00000100;
        6'b001000: Y_reg = 64'b00001000;
        6'b010000: Y_reg = 64'b00010000;
        6'b100000: Y_reg = 64'b00100000;
        6'b000000: Y_reg = 64'b01000000;
        default: Y_reg = 64'b00000000;
    endcase
end

always @(posedge ABCDEFGH[7]) begin  // Only respond to MSB of ABCDEFGH
    if (stage == 6'b000000) begin
        stage <= 6'b000001;
        Y <= Y_reg;
    end
    else begin
        stage <= {stage[4:0], 1'b0};
        Y <= Y_reg;
    end
end

endmodule