module edge_detector (
    input clk,
    input [7:0] in,
    output reg [7:0] anyedge
);

reg [7:0] prev_in;
reg [2:0] count;

always @(posedge clk) begin
    prev_in <= in;
    count <= count + 1;
end

always @(posedge clk) begin
    if (prev_in != in) begin
        anyedge <= {anyedge[6:0], 1'b1};
    end else begin
        anyedge <= {anyedge[6:0], 1'b0};
    end
end

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

edge_detector detector (
    .clk(clk),
    .in(in),
    .anyedge(anyedge)
);

endmodule