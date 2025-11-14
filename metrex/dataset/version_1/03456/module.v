
module comparator_mux (
    input [1:0] comp_in1, // 2-bit input for the comparator
    input [1:0] comp_in2, // 2-bit input for the comparator
    input [7:0] mux_in, // 4 2-bit inputs for the multiplexer
    input [1:0] select, // 2-bit select input for the multiplexer
    input control, // Control input to choose between the comparator and the multiplexer
    output [1:0] out // 2-bit output from the selected module
);

    // Comparator module
    wire [1:0] comp_out;
    // comparator comp(
    //     .in1(comp_in1),
    //     .in2(comp_in2),
    //     .out(comp_out)
    // );

    // Multiplexer module
    wire [1:0] mux_out;
    // mux4to1 mux(
    //     .in0(mux_in[1:0]),
    //     .in1(mux_in[3:2]),
    //     .in2(mux_in[5:4]),
    //     .in3(mux_in[7:6]),
    //     .sel(select),
    //     .out(mux_out)
    // );

    // Output selection based on control input
    assign out = control ? mux_out : comp_out;

endmodule
module comparator (
    input [1:0] in1, // 2-bit input 1
    input [1:0] in2, // 2-bit input 2
    output [1:0] out // 2-bit output
);

    assign out[0] = (in1[0] > in2[0]) ? 1'b1 : 1'b0;
    assign out[1] = (in1[1] > in2[1]) ? 1'b1 : 1'b0;
    assign out = (in1 == in2) ? 2'b11 : out;

endmodule
module mux4to1 (
    input [1:0] in0, // 2-bit input 0
    input [1:0] in1, // 2-bit input 1
    input [1:0] in2, // 2-bit input 2
    input [1:0] in3, // 2-bit input 3
    input [1:0] sel, // 2-bit select input
    output [1:0] out // 2-bit output
);

    assign out = (sel == 2'b00) ? in0 :
                 (sel == 2'b01) ? in1 :
                 (sel == 2'b10) ? in2 :
                                  in3;

endmodule