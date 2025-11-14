// SVA checker for shift_register
module shift_register_sva (
  input logic        clk,
  input logic [7:0]  data_in1,
  input logic [7:0]  data_in2,
  input logic [7:0]  q_out
);
  // Validate $past usage
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Wiring consistency
  assert property (q_out == shift_reg[7]);

  // One-cycle update relations
  assert property (disable iff(!past_valid) shift_reg[0] == $past(data_in1));
  genvar i;
  generate
    for (i = 1; i <= 6; i++) begin : g_shift_chain
      assert property (disable iff(!past_valid) shift_reg[i] == $past(shift_reg[i-1]));
    end
  endgenerate
  assert property (disable iff(!past_valid) shift_reg[7] == $past(data_in2));
  assert property (disable iff(!past_valid) q_out        == $past(data_in2));

  // End-to-end latency summary for data_in1 path
  assert property (1'b1 |-> ##7 (shift_reg[6] == $past(data_in1,7)));

  // Sanity: no X/Z on output after first valid cycle
  assert property (disable iff(!past_valid) !$isunknown(q_out));

  // Coverage
  cover property ($changed(data_in2) ##1 (q_out == $past(data_in2)));
  cover property ($changed(data_in1) ##7 (shift_reg[6] == $past(data_in1,7)));
  cover property (($changed(data_in1) && $changed(data_in2))
                  ##1 (shift_reg[0] == $past(data_in1) && q_out == $past(data_in2)));
endmodule

bind shift_register shift_register_sva u_shift_register_sva (
  .clk(clk),
  .data_in1(data_in1),
  .data_in2(data_in2),
  .q_out(q_out)
);