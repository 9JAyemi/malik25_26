
module top_module (
    input clk, // Clock input
    input reset, // Synchronous active-high reset
    input ce, // Clock enable for the counter
    input ctrl, // Control signal for the counter
    output reg [11:0] out // 12-bit output from the combined modules
);

wire [3:0] counter_out;
wire [15:0] decoder_out;

counter cnt (
    .clk(clk),
    .rst_n(reset),
    .ce(ce),
    .ctrl(ctrl),
    .count(counter_out)
);

decoder dec (
    .SEL(counter_out[1:0]),
    .OUT(decoder_out)
);

always @(*) begin
    out <= decoder_out[11:0];
end

endmodule
module counter (
    input clk,
    input rst_n,
    input ce,
    input ctrl,
    output reg [3:0] count
);

always @(posedge clk or posedge rst_n) begin
    if (rst_n) begin
        count <= 4'b0;
    end else if (ce) begin
        if (ctrl) begin
            count <= count + 1;
        end else begin
            count <= count - 1;
        end
    end
end

endmodule
module decoder (
    input [1:0] SEL,
    output reg [15:0] OUT
);

always @(*) begin
    case (SEL)
        2'b00: OUT = 16'b0000_0000_0000_0001;
        2'b01: OUT = 16'b0000_0000_0000_0010;
        2'b10: OUT = 16'b0000_0000_0000_0100;
        2'b11: OUT = 16'b0000_0000_0000_1000;
        default: OUT = 16'b0000_0000_0000_0000;
    endcase
end

endmodule