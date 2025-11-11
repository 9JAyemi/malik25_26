
module comparator_2bit (
  input [1:0] A,
  input [1:0] B,
  output equal,
  output greater
);

  assign equal = (A == B);
  assign greater = (A > B);

endmodule
module and_nor (
  input a,
  input b,
  output y
);

  assign y = ~(a | b);

endmodule
module greater_than (
  input clk,
  input reset,
  input [7:0] A,
  input [7:0] B,
  output result
);

  wire [1:0] comp_out [3:0];
  wire and_out;
  reg and_out_reg;

  comparator_2bit comp0(.A(A[7:6]), .B(B[7:6]), .equal(comp_out[0][0]), .greater(comp_out[0][1]));
  comparator_2bit comp1(.A(A[5:4]), .B(B[5:4]), .equal(comp_out[1][0]), .greater(comp_out[1][1]));
  comparator_2bit comp2(.A(A[3:2]), .B(B[3:2]), .equal(comp_out[2][0]), .greater(comp_out[2][1]));
  comparator_2bit comp3(.A(A[1:0]), .B(B[1:0]), .equal(comp_out[3][0]), .greater(comp_out[3][1]));

  and_nor and_gate(.a(comp_out[3][1]), .b(and_out_reg), .y(and_out));

  reg [3:0] result_reg;
  
  wire or_gate;
  assign or_gate = comp_out[3][0] || and_out_reg;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      result_reg <= 4'b0;
      and_out_reg <= 1'b0;
    end else begin
      result_reg <= {result_reg[2:0], or_gate};
      and_out_reg <= and_out;
    end
  end

  assign result = result_reg[3];

endmodule