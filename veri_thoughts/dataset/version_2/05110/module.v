module Behavioral_PE (
    input wire in2,
    input wire in1,
    input wire in0,
    output reg out1,
    output reg out0
);

reg [2:0] input_reg;

always @(*) begin
    input_reg = {in2, in1, in0};
    case (input_reg)
        3'b000, 3'b111:
            begin
                out1 = 1;
                out0 = 0;
            end
        3'b001, 3'b010, 3'b100, 3'b011, 3'b101, 3'b110:
            begin
                out1 = 0;
                out0 = 1;
            end
        default:
            begin
                out1 = 0;
                out0 = 0;
            end
    endcase
end

endmodule