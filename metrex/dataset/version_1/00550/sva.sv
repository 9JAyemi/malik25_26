// SVA checker for mux4to1_enable
// Binds to the DUT; no DUT edits required.

module mux4to1_enable_sva(
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic       ena,
  input logic       out
);

  // On each posedge of ena, out must capture in[sel] (after NBA)
  property p_capture;
    @(posedge ena) ##0 out == in[sel];
  endproperty
  a_capture: assert property(p_capture);

  // Inputs must be known at the sampling edge; out must be known after update
  a_no_x_inputs_at_ena: assert property(@(posedge ena) !$isunknown({ena, sel, in}));
  a_no_x_out_after_update: assert property(@(posedge ena) ##0 !$isunknown(out));

  // Output can only change coincident with a rising ena
  a_out_changes_only_on_ena: assert property(@(posedge out or negedge out) $rose(ena));

  // sel must be a valid index when sampled
  a_sel_in_range: assert property(@(posedge ena) sel inside {[0:3]});

  // Redundant but clearer per-select mapping checks
  a_map0: assert property(@(posedge ena) (sel==2'b00) |-> ##0 out==in[0]);
  a_map1: assert property(@(posedge ena) (sel==2'b01) |-> ##0 out==in[1]);
  a_map2: assert property(@(posedge ena) (sel==2'b10) |-> ##0 out==in[2]);
  a_map3: assert property(@(posedge ena) (sel==2'b11) |-> ##0 out==in[3]);

  // Coverage: exercise each select at an enable edge and both output values
  c_sel0: cover property(@(posedge ena) sel==2'b00);
  c_sel1: cover property(@(posedge ena) sel==2'b01);
  c_sel2: cover property(@(posedge ena) sel==2'b10);
  c_sel3: cover property(@(posedge ena) sel==2'b11);
  c_out0: cover property(@(posedge ena) ##0 out==1'b0);
  c_out1: cover property(@(posedge ena) ##0 out==1'b1);

endmodule

bind mux4to1_enable mux4to1_enable_sva u_mux4to1_enable_sva(.in(in), .sel(sel), .ena(ena), .out(out));

// Optional (if placing assertions inside the DUT instead of bind), you can also sanity-check the
// internal selected_input width/assignment quirk:
// assert property (@(posedge ena) selected_input[3:1]==3'b000 && selected_input[0]==in[sel]);