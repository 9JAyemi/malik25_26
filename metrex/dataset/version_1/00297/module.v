
module top_module (
    input [15:0] a,
    input [15:0] b,
    input [3:0] shift,
    input select,
    output [15:0] out
);

    // 16-bit adder
    wire [15:0] adder_out;
    assign adder_out = a + b;

    // 4-bit shifter
    wire [15:0] shifter_out;
    assign shifter_out = (shift == 4'd0) ? adder_out : (shift == 4'd1) ? {adder_out[14:0], 1'b0} :
                         (shift == 4'd2) ? {adder_out[13:0], 2'b00} : (shift == 4'd3) ? {adder_out[12:0], 3'b000} :
                         (shift == 4'd4) ? {adder_out[11:0], 4'b0000} : (shift == 4'd5) ? {adder_out[10:0], 5'b00000} :
                         (shift == 4'd6) ? {adder_out[9:0], 6'b000000} : (shift == 4'd7) ? {adder_out[8:0], 7'b0000000} :
                         (shift == 4'd8) ? {adder_out[7:0], 8'b00000000} : (shift == 4'd9) ? {adder_out[6:0], 9'b000000000} :
                         (shift == 4'd10) ? {adder_out[5:0], 10'b0000000000} : (shift == 4'd11) ? {adder_out[4:0], 11'b00000000000} :
                         (shift == 4'd12) ? {adder_out[3:0], 12'b000000000000} : (shift == 4'd13) ? {adder_out[2:0], 13'b0000000000000} :
                         (shift == 4'd14) ? {adder_out[1:0], 14'b00000000000000} : (shift == 4'd15) ? {adder_out[0], 15'b000000000000000} : 16'b0;

    // Functional module for bitwise OR
    wire [15:0] or_out;
    assign or_out = adder_out | shifter_out;

    // Output selection
    assign out = (select) ? shifter_out | or_out : adder_out | or_out;

endmodule