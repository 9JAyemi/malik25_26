
module rotator(
    input clk,
    input reset,
    input select,
    input [3:0] data_in,
    output [3:0] data_out
);

reg [3:0] shift_reg;

always @(posedge clk) begin
    if (reset) begin
        shift_reg <= 4'b0000;
    end else if (select) begin
        shift_reg <= {shift_reg[2:0], shift_reg[3]};
    end else begin
        shift_reg[3:1] <= shift_reg[2:0];
        shift_reg[0] <= shift_reg[3];
    end
end

assign data_out = shift_reg;

endmodule

module splitter(
    input clk,
    input reset,
    input [7:0] data_in,
    output [3:0] data_out_lo,
    output [3:0] data_out_hi
);

reg [3:0] data_out_lo_reg;
reg [3:0] data_out_hi_reg;

always @(posedge clk) begin
    if (reset) begin
        data_out_lo_reg <= 4'b0000;
        data_out_hi_reg <= 4'b0000;
    end else begin
        data_out_lo_reg <= data_in[3:0];
        data_out_hi_reg <= data_in[7:4];
    end
end

assign data_out_lo = data_out_lo_reg;
assign data_out_hi = data_out_hi_reg;

endmodule

module top_module(
    input clk,
    input reset,
    input select,
    input [7:0] data_in,
    output [3:0] data_out_lo,
    output [3:0] data_out_hi
);

wire [3:0] rotator_out;
wire [3:0] splitter_out_lo;
wire [3:0] splitter_out_hi;

rotator rotator_inst(
    .clk(clk),
    .reset(reset),
    .select(select),
    .data_in(data_in[3:0]),
    .data_out(rotator_out)
);

splitter splitter_inst(
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .data_out_lo(splitter_out_lo),
    .data_out_hi(splitter_out_hi)
);

reg [3:0] data_out_lo_reg;
reg [3:0] data_out_hi_reg;

always @(posedge clk) begin
    if (reset) begin
        data_out_lo_reg <= 4'b0000;
        data_out_hi_reg <= 4'b0000;
    end else if (select) begin
        data_out_lo_reg <= rotator_out;
        data_out_hi_reg <= rotator_out;
    end else begin
        data_out_lo_reg <= splitter_out_lo;
        data_out_hi_reg <= splitter_out_hi;
    end
end

assign data_out_lo = data_out_lo_reg;
assign data_out_hi = data_out_hi_reg;

endmodule
