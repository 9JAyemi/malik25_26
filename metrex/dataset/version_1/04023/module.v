module mux_parity (
    input [7:0] a, // 8-bit input a
    input [7:0] b, // 8-bit input b
    input [7:0] c, // 8-bit input c
    input [7:0] d, // 8-bit input d
    input sel_a, // Select input 1 for 4-to-1 MUX
    input sel_b, // Select input 2 for 4-to-1 MUX
    output reg [7:0] out, // 8-bit output with parity bit removed
    output reg error_flag // Error flag, set to 1 if there is a parity error
);

// 4-to-1 MUX
wire [7:0] mux_out;
mux_4to1 mux_inst (
    .a(a),
    .b(b),
    .c(c),
    .d(d),
    .sel_a(sel_a),
    .sel_b(sel_b),
    .out(mux_out)
);

// Parity bit checker
wire [7:0] data_in;
assign data_in = mux_out;
wire parity_bit;
assign parity_bit = ^data_in;
always @* begin
    if (parity_bit == 1'b1) begin
        error_flag = 1'b1;
        out = 8'b0;
    end else begin
        error_flag = 1'b0;
        out = data_in;
    end
end

endmodule

// 4-to-1 MUX module
module mux_4to1 (
    input [7:0] a, // 8-bit input a
    input [7:0] b, // 8-bit input b
    input [7:0] c, // 8-bit input c
    input [7:0] d, // 8-bit input d
    input sel_a, // Select input 1 for 4-to-1 MUX
    input sel_b, // Select input 2 for 4-to-1 MUX
    output reg [7:0] out // 8-bit output
);

always @* begin
    case ({sel_a, sel_b})
        2'b00: out = a;
        2'b01: out = b;
        2'b10: out = c;
        2'b11: out = d;
    endcase
end

endmodule