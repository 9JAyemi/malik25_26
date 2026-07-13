
module byte_swap (
    input [7:0] in,
    output [7:0] out
);
    assign out = {in[7], in[6], in[5], in[4], in[3], in[2], in[1], in[0]};
endmodule

module edge_detect (
    input [7:0] in,
    input clk,
    output reg anyedge
);
    reg [7:0] prev_in;
    
    always @(posedge clk) begin
        if (in != prev_in) begin
            anyedge <= 1;
        end else begin
            anyedge <= 0;
        end
        prev_in <= in;
    end
endmodule

module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] in,   // Input vector
    output reg anyedge    // Output signal indicating edge transition
);
    wire [7:0] swapped_in;
    wire edge_detected;
    
    byte_swap bs(in, swapped_in);
    edge_detect ed(swapped_in, clk, edge_detected);

    always @(posedge clk) begin
        if (reset) begin
            anyedge <= 0;
        end else begin
            anyedge <= edge_detected;
        end
    end
endmodule
