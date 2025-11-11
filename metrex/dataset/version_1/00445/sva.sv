// SVA for four_to_two: concise, high-quality checks and coverage.
// Provide a sampling clock from the environment (tb or harness).

module four_to_two_sva
  #(parameter bit HAS_RESET = 0)
  (input logic        clk,
   input logic        rst_n,     // tie 1'b1 if no reset
   input logic [3:0]  in_data,
   input logic [1:0]  out_data);

  default disable iff (HAS_RESET ? !rst_n : 1'b0);

  // Functional correctness with X-safety: when input is known, output is known and correct.
  property p_mapping_known;
    !$isunknown(in_data)
      |-> (!$isunknown(out_data) &&
           (out_data === ((in_data[3:2] == 2'b00) ? in_data[1:0] : 2'b00)));
  endproperty
  assert property (@(posedge clk) p_mapping_known);

  // Combinational stability: if input holds, output holds.
  assert property (@(posedge clk)
    ($stable(in_data) && !$isunknown(in_data)) |-> $stable(out_data));

  // Minimal functional coverage
  cover property (@(posedge clk) (in_data == 4'b0000 && out_data == 2'b00));
  cover property (@(posedge clk) (in_data == 4'b0001 && out_data == 2'b01));
  cover property (@(posedge clk) (in_data == 4'b0010 && out_data == 2'b10));
  cover property (@(posedge clk) (in_data == 4'b0011 && out_data == 2'b11));
  cover property (@(posedge clk) (in_data inside {[4:15]} && out_data == 2'b00));

endmodule

// Bind example (provide a clock from your testbench/environment):
// bind four_to_two four_to_two_sva #(.HAS_RESET(0))
//   sva_i (.clk(tb_clk), .rst_n(1'b1), .in_data(in_data), .out_data(out_data));