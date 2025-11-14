
module shift_register_3 (
    input clk,
    input reset,
    input [2:0] data_in,
    input shift,
    output [2:0] data_out
);

reg [2:0] reg_data;

always @(posedge clk) begin
    if (reset)
        reg_data <= 3'b0;
    else if (shift)
        reg_data <= {reg_data[1:0], data_in[2]};
end

assign data_out = reg_data;

endmodule

module shift_register_8 (
    input clk,
    input reset,
    input [7:0] data_in,
    input shift,
    output [7:0] data_out
);

reg [7:0] reg_data;

always @(posedge clk) begin
    if (reset)
        reg_data <= 8'b0;
    else if (shift)
        reg_data <= {reg_data[6:0], data_in[7]};
end

assign data_out = reg_data;

endmodule

module binary_counter (
    input clk,
    input reset,
    input enable,
    input load,
    input [7:0] data,
    output reg [2:0] count
);

wire [2:0] shift_reg_out;
wire [7:0] shift_reg_8_out;

shift_register_3 shift_reg_3_inst (
    .clk(clk),
    .reset(reset),
    .data_in(count),
    .shift(enable),
    .data_out(shift_reg_out)
);

shift_register_8 shift_reg_8_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data),
    .shift(load),
    .data_out(shift_reg_8_out)
);

always @(posedge clk) begin
    if (reset)
        count <= 3'b0;
    else if (load)
        count <= shift_reg_8_out[2:0];
    else if (enable)
        count <= count + 1;
end

endmodule
