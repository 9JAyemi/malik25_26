
module rotator(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output reg [99:0] out
);

reg [99:0] shift_reg;
reg [3:0] counter;

always @(posedge clk) begin
    if (load) begin
        shift_reg <= data;
    end else begin
        if (ena[0]) begin
            shift_reg <= {shift_reg[98:0], shift_reg[99]};
        end
        if (ena[1]) begin
            shift_reg <= {shift_reg[1:99], shift_reg[0]};
        end
    end
    out <= shift_reg;
end

endmodule
module counter(
    input clk,
    input reset,
    output reg [3:0] out
);

always @(posedge clk) begin
    if (reset) begin
        out <= 4'b0000;
    end else begin
        out <= out + 1;
    end
end

endmodule
module and_gate(
    input [99:0] in1,
    input [3:0] in2,
    output reg [99:0] out
);

always @(in1 or in2) begin
    out = in1 & (in2 << 96);
end

endmodule
module top_module(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output reg [3:0] counter_out,
    output reg [99:0] rotator_out,
    output reg [99:0] final_out
);

rotator rotator_inst(
    .clk(clk),
    .load(load),
    .ena(ena),
    .data(data),
    .out(rotator_out)
);

counter counter_inst(
    .clk(clk),
    .reset(load),
    .out(counter_out)
);

and_gate and_gate_inst(
    .in1(rotator_out),
    .in2(counter_out),
    .out(final_out)
);

endmodule