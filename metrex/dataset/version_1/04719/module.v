module edge_detector (
    input clk,
    input [7:0] in,
    output reg [7:0] anyedge
);

reg [7:0] prev_in;
reg [7:0] curr_in;
reg [7:0] edge_detected;

parameter IDLE = 2'b00;
parameter DETECT = 2'b01;
parameter OUTPUT = 2'b10;

reg [1:0] state;

always @(posedge clk) begin
    case (state)
        IDLE: begin
            curr_in <= in;
            prev_in <= curr_in;
            edge_detected <= 8'b0;
            state <= DETECT;
        end
        DETECT: begin
            curr_in <= in;
            if (curr_in != prev_in) begin
                edge_detected <= curr_in & ~prev_in;
                state <= OUTPUT;
            end else begin
                state <= IDLE;
            end
            prev_in <= curr_in;
        end
        OUTPUT: begin
            anyedge <= edge_detected;
            state <= IDLE;
        end
    endcase
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