// SVA for binary_to_gray
// Bind this file to the DUT:
//   bind binary_to_gray binary_to_gray_sva sva_i (.*);

module binary_to_gray_sva (
  input logic        clk,
  input logic [3:0]  bin_in,
  input logic [3:0]  gray_out,
  input logic [3:0]  gray_reg,
  input logic [1:0]  state
);

  function automatic [3:0] gray_func (input [3:0] b);
    gray_func = {b[3], b[3]^b[2], b[2]^b[1], b[1]^b[0]};
  endfunction

  default clocking @(posedge clk); endclocking
  default disable iff ($isunknown(state));

  // FSM behavior
  a_00_to_01:         assert property (state==2'b00 |=> state==2'b01);
  a_01_to_00:         assert property (state==2'b01 |=> state==2'b00);
  a_illegal_to_00:    assert property ((state inside {2'b10,2'b11}) |=> state==2'b00);

  // Output is driven by the internal register
  a_out_conn:         assert property ((!$isunknown(gray_out) && !$isunknown(gray_reg)) |-> (gray_out == gray_reg));

  // Functional correctness and timing
  a_gray_update_ok:   assert property (($past(state)==2'b01 && !$isunknown($past(bin_in)))
                                       |-> (state==2'b00 && gray_out == gray_func($past(bin_in))));
  a_hold_when_s0:     assert property (($past(state)==2'b00 && !$isunknown($past(gray_out)))
                                       |-> (state==2'b01 && gray_out == $past(gray_out)));
  a_reg_hold_not_s1:  assert property (($past(state)!=2'b01 && !$isunknown($past(gray_reg)))
                                       |-> (gray_reg == $past(gray_reg)));
  a_change_only_on_s1:assert property ((!$isunknown($past(gray_out)) && (gray_out != $past(gray_out)))
                                       |-> ($past(state)==2'b01));

  // Coverage
  cover_state_cycle:  cover property (state==2'b00 ##1 state==2'b01 ##1 state==2'b00);
  cover_update_event: cover property (($past(state)==2'b01 && !$isunknown($past(bin_in)))
                                       && (state==2'b00) && (gray_out == gray_func($past(bin_in))));
  genvar i;
  generate
    for (i=0;i<4;i++) begin : cbit
      cover property (($past(state)==2'b01 && !$isunknown($past(gray_out))) && (gray_out[i] != $past(gray_out[i])));
    end
  endgenerate

endmodule

bind binary_to_gray binary_to_gray_sva sva_i (.*);