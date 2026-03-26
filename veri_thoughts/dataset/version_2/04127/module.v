
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q,
    input [7:0] in,
    output [2:0] pos
);

wire [7:0] counter_out;
wire [7:0] register_out;
wire [2:0] priority_encoder_out;

counter my_counter (
    .clk(clk),
    .reset(reset),
    .out(counter_out)
);

register my_register (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(register_out)
);

priority_encoder my_priority_encoder (
    .in(in),
    .pos(priority_encoder_out)
);

assign pos = priority_encoder_out;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        q <= 8'b0;
    end else begin
        case (priority_encoder_out)
            3'b000: q <= register_out;
            3'b001: q <= counter_out;
            default: q <= 8'b0;
        endcase
    end
end

endmodule
module counter (
    input clk,
    input reset,
    output reg [7:0] out
);

always @(posedge clk or posedge reset) begin
    if (reset) begin
        out <= 8'b0;
    end else begin
        out <= out + 1;
    end
end

endmodule
module register (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q
);

always @(posedge clk or posedge reset) begin
    if (reset) begin
        q <= 8'b0;
    end else begin
        q <= d;
    end
end

endmodule
module priority_encoder (
    input [7:0] in,
    output reg [2:0] pos
);

always @(*) begin
    if (in[7]) pos <= 3'b111;
    else if (in[6]) pos <= 3'b110;
    else if (in[5]) pos <= 3'b101;
    else if (in[4]) pos <= 3'b100;
    else if (in[3]) pos <= 3'b011;
    else if (in[2]) pos <= 3'b010;
    else if (in[1]) pos <= 3'b001;
    else if (in[0]) pos <= 3'b000;
    else pos <= 3'b000;
end

endmodule