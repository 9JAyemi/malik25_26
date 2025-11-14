
module shifter (
    input [31:0] data_in,
    input [4:0] shift_amount,
    input [1:0] shift_direction,
    output [31:0] result,
    output zero
);

reg [31:0] stage1_out, stage2_out, stage3_out;

always @(*) begin
    case (shift_direction)
        2'b00: stage1_out = data_in >> shift_amount; // logical right shift
        2'b01: stage1_out = data_in << shift_amount; // logical left shift
        2'b10: stage1_out = { {32{data_in[31]}}, data_in[31:shift_amount] }; // arithmetic right shift
        default: stage1_out = 0;
    endcase
end

always @(*) begin
    stage2_out = stage1_out;
end

always @(*) begin
    stage3_out = stage2_out;
end

assign result = stage3_out;
assign zero = (result == 0);

endmodule