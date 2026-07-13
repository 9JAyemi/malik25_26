
module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    input d,
    output [11:0] out
);

// 6-to-1 multiplexer
wire [3:0] mux_out;
wire [2:0] dec_out;
priority_encoder pe(.in(sel), .out(dec_out));
decoder dec(.in(dec_out), .out(mux_out));

// Dual-edge triggered flip-flop
reg q, q_bar;
always @(posedge clk, negedge reset) begin
    if (reset == 1'b0) begin
        q <= 1'b0;
        q_bar <= 1'b1;
    end else begin
        q <= d;
        q_bar <= ~d;
    end
end

// Concatenation module
assign out = {mux_out, q, q_bar};

endmodule
module priority_encoder (
    input [2:0] in,
    output [2:0] out
);

assign out = 3'b000; // Default output

endmodule
module decoder (
    input [2:0] in,
    output [3:0] out
);

assign out = 4'b0000; // Default output

endmodule