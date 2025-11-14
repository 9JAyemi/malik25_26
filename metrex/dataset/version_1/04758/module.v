module edge_detector (
    input clk,
    input [7:0] in,
    output reg [7:0] out
);

reg [7:0] shift_reg [0:2];
reg [7:0] edge_reg;

always @(posedge clk) begin
    shift_reg[0] <= in;
    shift_reg[1] <= shift_reg[0];
    shift_reg[2] <= shift_reg[1];
    
    edge_reg <= (shift_reg[0] ^ shift_reg[2]) & shift_reg[1];
    
    out <= {1'b0, edge_reg[6:0]}; // Fixed part select order
end

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output reg [7:0] anyedge
);

wire [7:0] edge_out;

edge_detector ed (
    .clk(clk),
    .in(in),
    .out(edge_out)
);

always @* begin
    anyedge = edge_out;
end

endmodule