module transition_detector (
    input clk,
    input reset,
    input [31:0] in,
    output reg [31:0] out
);

reg [31:0] prev_in;

always @(posedge clk) begin
    if (reset) begin
        out <= 0;
        prev_in <= 0;
    end else begin
        if (in != prev_in) begin
            out <= out | (~in & prev_in);
        end
        prev_in <= in;
    end
end

endmodule

module shift_register (
    input clk,
    input reset,
    input [31:0] in,
    output reg [31:0] q
);

reg [2:0] counter;

always @(posedge clk) begin
    if (reset) begin
        q <= 0;
        counter <= 0;
    end else begin
        q <= {q[30:0], in};
        counter <= counter + 1;
        if (counter == 3) begin
            counter <= 0;
        end
    end
end

endmodule

module or_module (
    input [31:0] in1,
    input [31:0] in2,
    output reg [31:0] out
);

always @(*) begin
    out = in1 | in2;
end

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

wire [31:0] trans_out;
wire [31:0] shift_out;

transition_detector trans_detector (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(trans_out)
);

shift_register shift_reg (
    .clk(clk),
    .reset(reset),
    .in(trans_out),
    .q(shift_out)
);

or_module or_gate (
    .in1(trans_out),
    .in2(shift_out),
    .out(out)
);

endmodule