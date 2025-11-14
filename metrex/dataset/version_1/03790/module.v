
module mux_6to1 (
    input [2:0] sel,
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [3:0] in4,
    input [3:0] in5,
    output [3:0] out
);

    // Using a variable to store the internal output
    reg [3:0] mux_out_int;

    always @(*) begin
        case (sel)
            3'b000: mux_out_int = in0;
            3'b001: mux_out_int = in1;
            3'b010: mux_out_int = in2;
            3'b011: mux_out_int = in3;
            3'b100: mux_out_int = in4;
            3'b101: mux_out_int = in5;
            default: mux_out_int = 4'b0000;
        endcase
    end

    // Assign the internal output to the external output
    assign out = mux_out_int;

endmodule
