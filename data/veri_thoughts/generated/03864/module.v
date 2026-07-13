
module anyedge_detection (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

reg [7:0] prev_state;
reg [7:0] curr_state;
wire [7:0] edge_detect;

always @(posedge clk) begin
    prev_state <= curr_state;
    curr_state <= in;
end

assign edge_detect = prev_state ^ curr_state;
assign anyedge = edge_detect & curr_state;

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

anyedge_detection ed (
    .clk(clk),
    .in(in),
    .anyedge(anyedge)
);

endmodule
