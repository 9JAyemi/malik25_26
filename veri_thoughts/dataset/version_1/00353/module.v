
module bcd_counter (
    input clk,
    input reset,   // Synchronous active-high reset
    output reg [3:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0000;
        end else begin
            case (q)
                4'b0000: q <= 4'b0001;
                4'b0001: q <= 4'b0010;
                4'b0010: q <= 4'b0011;
                4'b0011: q <= 4'b0100;
                4'b0100: q <= 4'b0101;
                4'b0101: q <= 4'b0110;
                4'b0110: q <= 4'b0111;
                4'b0111: q <= 4'b1000;
                4'b1000: q <= 4'b1001;
                4'b1001: q <= 4'b0000;
                default: q <= 4'b0000;
            endcase
        end
    end

endmodule
module priority_encoder (
    input [3:0] in,
    output reg [1:0] out
);

    always @(*) begin
        out[1] = |in[3:2];
        out[0] = |in[1:0];
    end

endmodule
module multiplier (
    input [3:0] in,
    output reg [7:0] out
);

    always @(*) begin
        out = in << 4;
    end

endmodule
module top_module (
    input clk,
    input reset,   // Synchronous active-high reset
    output reg [3:0] ena,
    output reg [7:0] q
);

    wire [1:0] ena_wire;
    wire [3:0] bcd_out;
    wire [7:0] mult_out;

    bcd_counter counter(clk, reset, bcd_out);
    priority_encoder encoder(bcd_out, ena_wire);
    multiplier mult(bcd_out, mult_out);

    always @(*) begin
        ena = ena_wire;
        q = mult_out;
    end

endmodule