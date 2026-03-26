
module splitter (
    input [15:0] in,
    output [7:0] out_hi,
    output [7:0] out_lo
);
    assign out_hi = in[15:8];
    assign out_lo = in[7:0];
endmodule
module d_ff_counter (
    input clk,
    input [7:0] in,
    output reg [7:0] out
);
    always @(posedge clk) begin
        if (in == 8'd7) begin
            out <= 8'b0;
        end else begin
            out <= in + 1;
        end
    end
endmodule
module sum (
    input [7:0] in1,
    input [7:0] in2,
    output reg [7:0] out
);
    always @(in1, in2) begin
        out = in1 + in2;
    end
endmodule
module top_module (
    input clk,
    input [15:0] in,
    output [7:0] out_hi,
    output [7:0] out_lo,
    output reg [7:0] out_sum
);

    wire [7:0] sumResult;

    splitter splitter_inst (
        .in(in),
        .out_hi(out_hi),
        .out_lo(out_lo)
    );

    d_ff_counter d_ff_counter_inst (
        .clk(clk),
        .in(sumResult),
        .out(sumResult)
    );

    sum sum_inst (
        .in1(out_hi),
        .in2(out_lo),
        .out(out_sum)
    );

endmodule