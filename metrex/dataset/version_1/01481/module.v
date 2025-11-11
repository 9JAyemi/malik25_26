
module top_module (
    input clk,
    input reset,            // Synchronous active-high reset
    input [15:0] in,        // 16-bit input
    output [7:0] out_hi,    // 8-bit output for the upper byte
    output [7:0] out_lo,    // 8-bit output for the lower byte
    output [7:0] out         // 8-bit output for the final output
);

    wire [7:0] hi_reg;
    wire [7:0] lo_reg;
    wire [7:0] out_reg;

    barrel_shifter shifter(.in(in), .out(hi_reg));
    flip_flop lo_dff(.clk(clk), .reset(reset), .d(in[7:0]), .q(lo_reg));
    functional_module func(.in1(hi_reg), .in2(lo_reg), .out(out_reg));

    assign out_hi = hi_reg;
    assign out_lo = lo_reg;
    assign out = out_reg;

endmodule
module barrel_shifter (
    input [15:0] in,        // 16-bit input
    output [7:0] out    // 8-bit output for the upper byte
);

    assign out = in[15:8];

endmodule
module flip_flop (
    input clk,
    input reset,            // Asynchronous active-high reset
    input [7:0] d,          // 8-bit input
    output reg [7:0] q      // 8-bit output (complement of input)
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            q <= 8'h00;
        end else begin
            q <= ~d;
        end
    end

endmodule
module functional_module (
    input [7:0] in1,        // 8-bit input from the barrel shifter
    input [7:0] in2,        // 8-bit input from the flip-flop
    output [7:0] out    // 8-bit output (OR of the two inputs)
);

    assign out = in1 | in2;

endmodule