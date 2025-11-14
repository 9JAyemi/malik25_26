
module top_module(
    input clk,
    input reset,      // Asynchronous active-high reset
    output reg [31:0] out
);

    reg [3:0] counter_out_reg;
    wire [3:0] counter_out_next;

    counter counter_inst(.clk(clk), .reset(reset), .q(counter_out_next));

    always @ (posedge clk) begin
        if (reset) begin
            counter_out_reg <= 0;
        end else begin
            counter_out_reg <= counter_out_next;
        end
    end

    wire [31:0] selected_out;
    demux_1to256 demux_inst(.in(out), .sel(counter_out_reg), .out(selected_out));

    always @* begin
        out = {(selected_out[15:8] & {8{selected_out[7]}}) ,selected_out[7:0]};
    end

endmodule
module counter(
    input clk,
    input reset,      // Asynchronous active-high reset
    output reg [3:0] q
);

    always @ (posedge clk or posedge reset) begin
        if (reset) begin
            q <= 0;
        end else if (q == 15) begin
            q <= 0;
        end else begin
            q <= q + 1;
        end
    end

endmodule
module demux_1to256(
    input [31:0] in,
    input [3:0] sel,
    output reg [31:0] out
);

    always @* begin
        case (sel)
            4'b0000: out = in;
            4'b0001: out = {in[7:0], 24'b0};
            4'b0010: out = {in[15:0], 16'b0};
            4'b0011: out = {in[23:0], 8'b0};
            4'b0100: out = {in[31:24], 8'b0};
            4'b0101: out = {in[31:20], 12'b0};
            4'b0110: out = {in[31:16], 16'b0};
            4'b0111: out = {in[31:12], 20'b0};
            4'b1000: out = {in[31:8], 24'b0};
            4'b1001: out = {in[31:4], 28'b0};
            4'b1010: out = in;
            4'b1011: out = 32'b0;
            4'b1100: out = {in[7:0], 24'b0};
            4'b1101: out = {in[15:0], 16'b0};
            4'b1110: out = {in[23:0], 8'b0};
            4'b1111: out = in;
        endcase
    end

endmodule