
module wire_mux (
    input a,
    input b,
    input c,
    output w,
    output x,
    output y,
    output z
);
    assign w = a;
    assign x = b ? 1 : 0;
    assign y = b ? 1 : 0;
    assign z = c;
endmodule

module mux_sel (
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
        case (sel)
            3'b000: out = data0;
            3'b001: out = data1;
            3'b010: out = data2;
            3'b011: out = data3;
            3'b100: out = data4;
            3'b101: out = data5;
            default: out = 0;
        endcase
    end
endmodule

module top_module (
    input a,
    input b,
    input c,
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output [7:0] final_output
); 
    wire_mux mux_inst (
        .a(a),
        .b(b),
        .c(c),
        .w(final_output[3]),
        .x(final_output[2]),
        .y(final_output[1]),
        .z(final_output[0])
    );
    
    mux_sel sel_inst (
        .sel(sel),
        .data0(data0),
        .data1(data1),
        .data2(data2),
        .data3(data3),
        .data4(data4),
        .data5(data5),
        .out(final_output[7:4])
    );
endmodule
