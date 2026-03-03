
module final_module (
    input [1:0] comparator_output,
    input [2:0] up_down_output,
    input [3:0] A,
    input [3:0] B,
    output [4:0] final_output
);

reg [4:0] final_output_internal;

assign final_output = final_output_internal;

always @(*) begin
  case (comparator_output)
    2'b01: final_output_internal = up_down_output + A;
    2'b10: final_output_internal = up_down_output + B;
    default: final_output_internal = up_down_output;
  endcase
end

endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] A,
    input [3:0] B,
    input up_down,
    output [4:0] final_output
);

wire [1:0] comparator_output;
wire [2:0] up_down_output;

comparator comparator_inst (
    .A(A),
    .B(B),
    .OUT(comparator_output)
);

up_down_counter up_down_counter_inst (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .count(up_down_output)
);

final_module final_module_inst (
    .comparator_output(comparator_output),
    .up_down_output(up_down_output),
    .A(A),
    .B(B),
    .final_output(final_output)
);

endmodule

module comparator (
    input [3:0] A,
    input [3:0] B,
    output reg [1:0] OUT
);

always @(*) begin
    if (A > B) OUT = 2'b01;
    else if (A < B) OUT = 2'b10;
    else OUT = 2'b00;
end

endmodule

module up_down_counter (
    input clk,
    input reset,
    input up_down,
    output reg [2:0] count
);

always @(posedge clk, posedge reset) begin
    if (reset) count <= 3'b000;
    else begin
        if (up_down) count <= count + 1;
        else count <= count - 1;
    end
end

endmodule
