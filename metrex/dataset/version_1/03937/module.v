
module rotator (
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] out
);

reg [99:0] shift_reg;

always @(posedge clk) begin
    if (load) begin
        shift_reg <= data;
    end else begin
        case (ena)
            2'b00: shift_reg <= {shift_reg[98:0], shift_reg[99]};
            2'b01: shift_reg <= {shift_reg[1:0], shift_reg[99:2]};
            2'b10: shift_reg <= {shift_reg[0], shift_reg[99:1]};
            2'b11: shift_reg <= shift_reg;
        endcase
    end
end

assign out = shift_reg;

endmodule
module transition_detector (
    input clk,
    input reset,
    input [31:0] in,
    output reg out
);

reg [31:0] in_reg;
reg [31:0] in_delayed;

always @(posedge clk or negedge reset) begin
    if (!reset) begin
        in_reg <= 0;
        in_delayed <= 0;
        out <= 0;
    end else begin
        in_reg <= in;
        in_delayed <= in_reg;
        out <= (in_reg ^ in_delayed) & in_reg;
    end
end

endmodule
module functional_module (
    input [99:0] rotator_out,
    input transition_detector_out,
    output [131:0] out
);

assign out = {rotator_out, {30{transition_detector_out}}, transition_detector_out};

endmodule
module top_module (
    input clk,
    input reset,
    input load,
    input [1:0] ena,
    input [99:0] data,
    input [31:0] in,
    output [131:0] out
);

wire [99:0] rotator_out;
wire transition_detector_out;

rotator rotator_inst (
    .clk(clk),
    .load(load),
    .ena(ena),
    .data(data),
    .out(rotator_out)
);

transition_detector transition_detector_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(transition_detector_out)
);

functional_module functional_module_inst (
    .rotator_out(rotator_out),
    .transition_detector_out(transition_detector_out),
    .out(out)
);

endmodule