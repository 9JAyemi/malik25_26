
module binary_adder (
    input [7:0] input1,
    input [7:0] input2,
    input carry_in,
    output [7:0] sum,
    output carry_out,
    output overflow_flag
);

reg [8:0] stage1_out;
reg [8:0] stage2_out;
reg [8:0] stage3_out;
reg [8:0] stage4_out;
reg [8:0] stage5_out;
reg [8:0] stage6_out;
reg [8:0] stage7_out;
reg [9:0] stage8_out;
reg [1:0] overflow_check;

assign sum = stage8_out[7:0];
assign carry_out = stage8_out[8];

always @(*) begin
    stage1_out = input1 + input2 + carry_in;
end

always @(*) begin
    stage2_out = stage1_out + {1'b0, stage1_out[7:1]};
end

always @(*) begin
    stage3_out = stage2_out + {1'b0, stage2_out[6:0], stage2_out[7]};
end

always @(*) begin
    stage4_out = stage3_out + {1'b0, stage3_out[5:0], stage3_out[6]};
end

always @(*) begin
    stage5_out = stage4_out + {1'b0, stage4_out[4:0], stage4_out[5]};
end

always @(*) begin
    stage6_out = stage5_out + {1'b0, stage5_out[3:0], stage5_out[4]};
end

always @(*) begin
    stage7_out = stage6_out + {1'b0, stage6_out[2:0], stage6_out[3]};
end

always @(*) begin
    stage8_out = stage7_out + {1'b0, stage7_out[1:0], stage7_out[2]};
    overflow_check = stage7_out[8:7] + stage8_out[8:7];
end

assign overflow_flag = (overflow_check == 2'b10);

endmodule