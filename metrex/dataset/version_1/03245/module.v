
module top_module(
    input wire clk,
    input wire reset,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    output wire [15:0] final_out
);

reg [3:0] counter;
reg [15:0] input_num;

splitter splitter_inst(
    .input_num(input_num),
    .out_hi(out_hi),
    .out_lo(out_lo)
);

combiner combiner_inst(
    .out_hi(out_hi),
    .out_lo(out_lo),
    .final_out(final_out)
);

always @(posedge clk) begin
    if (reset) begin
        counter <= 4'd0;
        input_num <= 16'd0;
    end else begin
        counter <= counter + 1;
        input_num <= input_num + 1;
    end
end

endmodule

module splitter(
    input [15:0] input_num,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

assign out_hi = input_num[15:8];
assign out_lo = input_num[7:0];

endmodule

module combiner(
    input [7:0] out_hi,
    input [7:0] out_lo,
    output wire [15:0] final_out
);

assign final_out = {out_hi, out_lo};

endmodule
