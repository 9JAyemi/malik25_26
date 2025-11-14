
module rotator(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output reg [99:0] q
);

reg [99:0] shift_reg;
reg [6:0] shift_cnt;

always @(posedge clk) begin
    if (load) begin
        shift_reg <= data;
        shift_cnt <= 0;
    end else begin
        case (ena)
            2'b00: begin // right rotate
                shift_reg <= {shift_reg[1], shift_reg[99:2]};
                shift_cnt <= shift_cnt + 1;
            end
            2'b01: begin // left rotate
                shift_reg <= {shift_reg[99:1], shift_reg[0]};
                shift_cnt <= shift_cnt + 1;
            end
            default: begin // no rotation
                shift_reg <= shift_reg;
                shift_cnt <= 0;
            end
        endcase
    end
end

always @(posedge clk) begin
    q <= shift_reg;
end

endmodule
module top_module(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output reg [99:0] q
);

wire [99:0] rotator_out;

rotator rotator_inst(
    .clk(clk),
    .load(load),
    .ena(ena),
    .data(data),
    .q(rotator_out)
);

always @(*) begin
    q <= rotator_out;
end

endmodule