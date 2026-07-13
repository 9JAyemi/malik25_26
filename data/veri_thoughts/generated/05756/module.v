
module top_module (
    input clk,
    input reset,
    input [3:0] a,
    input [3:0] b,
    input [1:0] select,
    output reg [7:0] product
);

wire [3:0] booth_input;
wire [7:0] booth_output;

decoder_2to4 decoder_inst (
    .in(select),
    .out(booth_input)
);

booth_multiplier booth_inst (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .booth_input(booth_input[1:0]),
    .product(booth_output)
);

always @(posedge clk) begin
    if (reset) begin
        product <= 8'b0;
    end else begin
        product <= booth_output;
    end
end

endmodule
module decoder_2to4 (
    input [1:0] in,
    output reg [3:0] out
);

always @(*) begin
    case (in)
        2'b00: out = 4'b0001;
        2'b01: out = 4'b0010;
        2'b10: out = 4'b0100;
        2'b11: out = 4'b1000;
        default: out = 4'b0000;
    endcase
end

endmodule
module booth_multiplier (
    input clk,
    input reset,
    input [3:0] a,
    input [3:0] b,
    input [1:0] booth_input,
    output reg [7:0] product
);

reg [7:0] register_a;
reg [7:0] register_b;
reg [7:0] register_p;

always @(posedge clk) begin
    if (reset) begin
        register_a <= 8'b0;
        register_b <= 8'b0;
        register_p <= 8'b0;
    end else begin
        register_a <= {a, 4'b0};
        register_b <= b;

        case (booth_input)
            2'b00: begin
                register_p <= register_p + register_b;
            end
            2'b01: begin
                register_p <= register_p - register_b;
            end
            2'b10: begin
                register_p <= register_p + register_b;
            end
            2'b11: begin
                register_p <= register_p - register_b;
            end
        endcase

        register_a <= register_a >> 1;
    end
end

always @(*) begin
    product <= register_p;
end

endmodule