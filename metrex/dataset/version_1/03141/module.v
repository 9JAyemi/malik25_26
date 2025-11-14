
module top_module(
    input clk,
    input reset,
    input [7:0] d,
    input [3:0] sel,  // Changed from [7:0] to [3:0]
    input [7:0] a,
    input [7:0] b,
    output [7:0] out,
    output [8:0] sum
);

    // 4-to-1 Multiplexer
    wire [7:0] mux_out;
    mux_4to1 mux_inst(
        .d0(d),
        .d1(a),
        .d2(b),
        .d3(8'h00),
        .sel(sel[3:0]),  // Changed from sel to sel[3:0]
        .out(mux_out)
    );
    
    // 2-bit Adder
    wire [8:0] add_out;
    adder_2bit add_inst(
        .a(a),
        .b(b),
        .out(add_out)
    );
    
    // Sum Calculation
    wire [8:0] sum_temp;
    assign sum_temp = add_out + 9'h34;
    
    // Output Assignment
    assign out = mux_out;
    assign sum = sum_temp[8:1];
    
endmodule

module mux_4to1(
    input [7:0] d0,
    input [7:0] d1,
    input [7:0] d2,
    input [7:0] d3,
    input [3:0] sel,
    output reg [7:0] out
);

    always @(sel or d0 or d1 or d2 or d3) begin
        case(sel)
            4'b0000: out <= d0;
            4'b0001: out <= d1;
            4'b0010: out <= d2;
            4'b0011: out <= d3;
            default: out <= 8'h00;
        endcase
    end
endmodule

module adder_2bit(
    input [7:0] a,
    input [7:0] b,
    output reg [8:0] out
);

    always @(a or b) begin
        out <= {1'b0, a} + {1'b0, b};
    end
endmodule
