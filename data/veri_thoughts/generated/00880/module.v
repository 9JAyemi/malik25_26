module pipelined_xor_gate(input a, b, output out_assign, input clk);

  reg a_reg, b_reg;
  wire xor_out;
  reg out_assign_reg;

  assign xor_out = a_reg ^ b_reg;
  assign out_assign = out_assign_reg;

  always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
  end

  always @(posedge clk) begin
    out_assign_reg <= xor_out;
  end

endmodule

module pipeline_stage_1(input a, b, output reg a_reg, output reg b_reg, input clk);

  always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
  end

endmodule

module pipeline_stage_2(input xor_out, output reg out_assign_reg, input clk);

  always @(posedge clk) begin
    out_assign_reg <= xor_out;
  end

endmodule