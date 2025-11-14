
module nor_gate(
    input a,
    input b,
    output out
);
    wire temp1, temp2;
    not_gate not1(a, temp1);
    not_gate not2(b, temp2);
    and_gate and1(temp1, temp2, out);
endmodule
module shift_register(
    input clk,
    input rst,
    input data,
    output reg [2:0] out
);
    always @(posedge clk or negedge rst) begin
        if (~rst) begin
            out <= 3'b0;
        end else begin
            out[2:1] <= out[1:0];
            out[0] <= data;
        end
    end
endmodule
module or_module(
    input a,
    input [2:0] b,
    output out
);
    wire temp1, temp2;
    nor_gate nor1(a, b[0], temp1);
    nor_gate nor2(temp1, b[1], temp2);
    nor_gate nor3(temp2, b[2], out);
endmodule
module top_module(
    input a,
    input b,
    input clk,
    input rst,
    input data,
    output out
);
    wire [2:0] shift_out;
    shift_register shift_reg(clk, rst, data, shift_out);
    or_module or_mod(a, shift_out, out);
endmodule
module not_gate(
    input in,
    output out
);
    assign out = !in;
endmodule
module and_gate(
    input a,
    input b,
    output out
);
    assign out = a && b;
endmodule
module nor_gate_level(
    input a,
    input b,
    output out
);
    assign out = ~(a | b);
endmodule