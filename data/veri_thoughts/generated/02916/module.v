
module shift_register (
    input clk,
    input reset,
    input [7:0] data_in,
    input [1:0] shift_direction,
    input load,
    output reg [7:0] q
);

always @(posedge clk or negedge reset) begin
    if (!reset) begin
        q <= 8'd0;
    end else if (load) begin
        q <= data_in;
    end else begin
        if (shift_direction == 2'b00) begin
            q <= {q[6:0], q[7]};
        end else if (shift_direction == 2'b01) begin
            q <= {q[0], q[7:1]};
        end
    end
end

endmodule

module min_finder (
    input [7:0] a, b, c, d,
    output reg [7:0] min
);

always @(*) begin
    min = a;
    if (b < min) min = b;
    if (c < min) min = c;
    if (d < min) min = d;
end

endmodule

module top_module (
    input clk,
    input reset,
    input [7:0] data_in,
    input [1:0] shift_direction,
    input load,
    input [7:0] a, b, c, d,
    output [7:0] q,
    output [7:0] min,
    output [7:0] final_output
);

shift_register sr (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .shift_direction(shift_direction),
    .load(load),
    .q(q)
);

min_finder mf (
    .a(a),
    .b(b),
    .c(c),
    .d(d),
    .min(min)
);

assign final_output = min & q;

endmodule
