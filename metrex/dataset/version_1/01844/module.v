
module combinational_logic (
    input [2:0] vec,
    output reg out1,
    output reg out2,
    output reg out3
);

always @(*) begin
    out1 = vec[0];
    out2 = vec[1];
    out3 = vec[2];
end

endmodule

module shift_register (
    input clk,
    input serial_in,
    output reg serial_out
);

reg [2:0] shift_reg;

always @(posedge clk) begin
    shift_reg <= {shift_reg[1:0], serial_in};
    serial_out = shift_reg[2];
end

endmodule

module functional_module (
    input in1,
    input in2,
    input in3,
    input serial_out,
    output [3:0] final_output
);

assign final_output = {in1, in2, in3, serial_out};

endmodule

module top_module (
    input clk,
    input reset,
    input [2:0] vec,
    input serial_in,
    output [3:0] final_output
);

wire out1, out2, out3, serial_out;

combinational_logic comb(.vec(vec), .out1(out1), .out2(out2), .out3(out3));
shift_register shift_reg(.clk(clk), .serial_in(serial_in), .serial_out(serial_out));
functional_module func(.in1(out1), .in2(out2), .in3(out3), .serial_out(serial_out), .final_output(final_output));

endmodule
