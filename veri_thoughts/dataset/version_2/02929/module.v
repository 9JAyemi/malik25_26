
module full_adder (
    input a, b, cin,
    output cout, sum
);

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);

endmodule

module mux_6to1 (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [3:0] out
);

    always @(*) begin
        case(sel)
            3'b000: out = data0;
            3'b001: out = data1;
            3'b010: out = data2;
            3'b011: out = data3;
            3'b100: out = data4;
            3'b101: out = data5;
            default: out = 4'bXXXX;
        endcase
    end

endmodule

module final_module (
    input [3:0] mux_out,
    input [1:0] adder_out,
    output [3:0] out
);

    assign out = mux_out + adder_out;

endmodule

module top_module ( 
    input a, b, cin,
    output cout, sum,
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output [3:0] out
);

    wire [3:0] mux_out;  // Declared as a wire in the 'top_module'

    full_adder fa_inst (
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum),
        .cout(cout)
    );

    mux_6to1 mux_inst (
        .sel(sel),
        .data0(data0),
        .data1(data1),
        .data2(data2),
        .data3(data3),
        .data4(data4),
        .data5(data5),
        .out(mux_out)
    );

    final_module final_inst (
        .mux_out(mux_out),
        .adder_out({cout, sum}),
        .out(out)
    );

endmodule
