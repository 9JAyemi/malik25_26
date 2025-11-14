
module johnson_counter (
    input clk,              // Clock input
    input reset,            // Synchronous active-low reset
    output reg [3:0] out    // 4-bit output
);

reg [2:0] state = 3'b000;

always @(posedge clk) begin
    if (reset) begin
        state <= 3'b000;
    end else begin
        case (state)
            3'b000: state <= 3'b100;
            3'b100: state <= 3'b110;
            3'b110: state <= 3'b111;
            3'b111: state <= 3'b011;
            3'b011: state <= 3'b001;
            3'b001: state <= 3'b000;
            default: state <= 3'b000;
        endcase
    end
    out <= {state[2], state[1], state[0], out[3]};
end

endmodule
module half_word_comb (
    input [7:0] in_hi,      // Upper byte input
    input [7:0] in_lo,      // Lower byte input
    output reg [15:0] out   // 16-bit output
);

always @(*) begin
    out = {in_hi, in_lo};
end

endmodule
module top_module (
    input clk,              // Clock input
    input reset,            // Synchronous active-low reset
    input [7:0] in_hi,      // Upper byte input
    input [7:0] in_lo,      // Lower byte input
    output reg [79:0] out   // 80-bit output
);

wire [3:0] johnson_out;
wire [15:0] half_word_out;

johnson_counter jc (
    .clk(clk),
    .reset(reset),
    .out(johnson_out)
);

half_word_comb hw (
    .in_hi(in_hi),
    .in_lo(in_lo),
    .out(half_word_out)
);

always @(posedge clk or posedge reset) begin
    if (reset) begin
        out <= 80'b0;
    end else begin
        out <= {half_word_out, johnson_out};
    end
end

endmodule