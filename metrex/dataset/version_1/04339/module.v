
module barrel_shifter_16bit (
    input [15:0] data,
    input [3:0] shift_amount,
    output [15:0] shifted_data
);

reg [15:0] stage1_data;
reg [15:0] stage2_data;
reg [15:0] stage3_data;
reg [15:0] stage4_data;



always @(data, shift_amount) begin
    stage1_data = data;
    stage2_data = stage1_data >> {2'b00, shift_amount[1:0]};
    stage3_data = stage2_data >> {shift_amount[3:2], 2'b00};
    stage4_data = stage3_data >> {shift_amount[3:2], 2'b00};
end

assign shifted_data = {stage4_data[7:0], stage4_data[15:8]};

endmodule
