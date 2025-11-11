module top_module( 
    input clk,
    input reset,      // Synchronous active-high reset
    input a,b,c,
    input [31:0] in,
    output [31:0] out,
    output w,x,y,z );

    wire [31:0] mux_out;
    wire [31:0] reverse_out;

    // Multiplexer module
    mux_3to4 mux_inst (
        .clk(clk),
        .reset(reset),
        .a(a),
        .b(b),
        .c(c),
        .w(w),
        .x(x),
        .y(y),
        .z(z),
        .mux_out(mux_out)
    );

    // Byte reversal module
    byte_reversal br_inst (
        .clk(clk),
        .reset(reset),
        .in(in),
        .out(reverse_out)
    );

    // XOR module
    xor_module xor_inst (
        .in1(mux_out),
        .in2(reverse_out),
        .out(out)
    );

endmodule

module mux_3to4 (
    input clk,
    input reset,
    input a, b, c,
    output w, x, y, z,
    output [31:0] mux_out
);

    reg [31:0] mux_reg;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            mux_reg <= 32'h0;
        end else begin
            case ({a, b, c})
                3'b000: mux_reg <= 32'h0;
                3'b001: mux_reg <= 32'h1;
                3'b010: mux_reg <= 32'h2;
                3'b011: mux_reg <= 32'h3;
                3'b100: mux_reg <= 32'h4;
                3'b101: mux_reg <= 32'h5;
                3'b110: mux_reg <= 32'h6;
                3'b111: mux_reg <= 32'h7;
            endcase
        end
    end

    assign mux_out = mux_reg;
    assign {w, x, y, z} = mux_reg[3:0];

endmodule

module byte_reversal (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

    reg [31:0] reverse_reg;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            reverse_reg <= 32'h0;
        end else begin
            reverse_reg <= {in[7:0], in[15:8], in[23:16], in[31:24]};
        end
    end

    assign out = reverse_reg;

endmodule

module xor_module (
    input [31:0] in1,
    input [31:0] in2,
    output [31:0] out
);

    assign out = in1 ^ in2;

endmodule