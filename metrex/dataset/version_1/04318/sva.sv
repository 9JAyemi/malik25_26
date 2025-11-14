// SVA for the given design. Bind these in your simulation.

module rising_edge_detector_sva(input clk, input [7:0] in, input [7:0] out, input [7:0] prev_in);
  default clocking cb @(posedge clk); endclocking

  // prev_in must track previous in
  ap_prev_updates: assert property ( !$isunknown($past(in)) |-> (prev_in == $past(in)) );

  // Update out on increase, hold otherwise
  ap_out_updates_on_rise: assert property ( (!$isunknown($past(prev_in)) && (in > $past(prev_in))) |-> (out == in) );
  ap_out_holds:           assert property ( (!$isunknown($past(prev_in)) && !(in > $past(prev_in))) |-> (out == $past(out)) );

  // Any change in out must be due to a detected increase
  ap_out_changes_imply_rise: assert property ( (!$isunknown($past(prev_in)) && !$isunknown($past(out)) && (out != $past(out))) |-> (in > $past(prev_in)) );

  // Coverage
  cp_rise:    cover property ( !$isunknown($past(prev_in)) && (in > $past(prev_in)) );
  cp_no_rise: cover property ( !$isunknown($past(prev_in)) && !(in > $past(prev_in)) );
endmodule

bind rising_edge_detector rising_edge_detector_sva red_sva(.clk(clk), .in(in), .out(out), .prev_in(prev_in));


module shift_register_sva(input clk, input [7:0] in, input [7:0] out, input [7:0] shift_reg);
  default clocking cb @(posedge clk); endclocking

  // Static width sanity check (flags RTL issue)
  initial begin
    assert ($bits({shift_reg[6:0], in}) == $bits(shift_reg))
      else $error("Width mismatch: {shift_reg[6:0], in} truncates into shift_reg");
  end

  // Given current RTL, shift_reg mirrors previous in; out mirrors previous shift_reg
  ap_sr_next:   assert property ( !$isunknown($past(in))        |-> (shift_reg == $past(in)) );
  ap_out_next:  assert property ( !$isunknown($past(shift_reg)) |-> (out == $past(shift_reg)) );
  ap_out_in2:   assert property ( !$isunknown($past(in,2))      |-> (out == $past(in,2)) );

  // Coverage
  cp_sr_moves:  cover property ($changed(shift_reg));
  cp_out_moves: cover property ($changed(out));
endmodule

bind shift_register shift_register_sva sr_sva(.clk(clk), .in(in), .out(out), .shift_reg(shift_reg));


module top_module_sva(input clk,
                      input [7:0] in,
                      input [2:0] select,
                      input [7:0] q,
                      input [7:0] rising_edge_out,
                      input [7:0] shift_reg_out);
  default clocking cb @(posedge clk); endclocking

  // data_selector behavior (sampled on clk)
  ap_sel_in:     assert property ( (select == 3'b000) |-> (q == in) );
  ap_sel_stored: assert property ( (select == 3'b001) |-> (q == shift_reg_out) );
  ap_sel_def:    assert property ( !(select inside {3'b000,3'b001}) |-> (q == 8'h00) );

  // Pipeline integration: shift_reg_out is rising_edge_out delayed by 2 cycles (per current RTL)
  ap_srout_is_red_delayed2: assert property ( !$isunknown($past(rising_edge_out,2)) |-> (shift_reg_out == $past(rising_edge_out,2)) );

  // Coverage of selector modes
  cp_sel0:    cover property (select == 3'b000);
  cp_sel1:    cover property (select == 3'b001);
  cp_sel_def: cover property (!(select inside {3'b000,3'b001}));
endmodule

bind top_module top_module_sva top_sva(.clk(clk),
                                       .in(in),
                                       .select(select),
                                       .q(q),
                                       .rising_edge_out(rising_edge_out),
                                       .shift_reg_out(shift_reg_out));