
module priority_encoder_shift_register (
    input clk,
    input areset,  // async active-high reset to zero
    input load,
    input ena,
    input [7:0] in,
    output reg [6:0] out
);

    // Priority Encoder
    wire [2:0] gray_code;
    wire [2:0] decimal_code;
    wire [8:0] in_gray;
    assign in_gray = {in[7], in[7]^in[6], in[6]^in[5], in[5]^in[4], in[4]^in[3], in[3]^in[2], in[2]^in[1], in[1]^in[0]};
    gray_to_decimal_converter gray_to_decimal(.gray(in_gray[2:0]), .decimal(decimal_code));

    // Shift Register
    reg [3:0] shift_reg;
    always @(posedge clk or posedge areset) begin
        if (areset) begin
            shift_reg <= 4'b0;
        end else if (load) begin
            shift_reg <= in[3:0];
        end else if (ena) begin
            shift_reg <= {shift_reg[2:0], shift_reg[3]};
        end
    end

    // Mux
    wire [3:0] mux_out;
    assign mux_out = load ? in[3:0] : shift_reg;

    // Output
    wire [6:0] sum;
    adder add(.a(decimal_code), .b(mux_out), .sum(sum));
    always @* begin
        out = sum;
    end

endmodule
module gray_to_decimal_converter (
    input [2:0] gray,
    output reg [2:0] decimal
);

    always @* begin
        case (gray)
            3'b000: decimal = 3'b000;
            3'b001: decimal = 3'b001;
            3'b010: decimal = 3'b011;
            3'b011: decimal = 3'b010;
            3'b100: decimal = 3'b110;
            3'b101: decimal = 3'b111;
            3'b110: decimal = 3'b101;
            3'b111: decimal = 3'b100;
        endcase
    end
endmodule
module adder (
    input [2:0] a,
    input [3:0] b,
    output reg [6:0] sum
);

    always @* begin
        sum = {1'b0, a} + b;
    end
endmodule