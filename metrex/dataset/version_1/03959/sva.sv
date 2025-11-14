// SVA for mux4to1
module mux4to1_sva #(parameter W=8) (
  input               clock,
  input               reset,
  input  [W-1:0]      in_0,
  input  [W-1:0]      in_1,
  input  [W-1:0]      in_2,
  input  [W-1:0]      in_3,
  input  [1:0]        sel,
  input  [W-1:0]      out,
  input  [W-1:0]      selected_input
);

  function automatic [W-1:0] pick(input [1:0] s,
                                  input [W-1:0] a,b,c,d);
    case (s)
      2'b00: pick = a;
      2'b01: pick = b;
      2'b10: pick = c;
      2'b11: pick = d;
      default: pick = {W{1'bx}};
    endcase
  endfunction

  default clocking cb @(posedge clock); endclocking

  // Asynchronous reset drives zeros immediately (same timestep) and holds during reset
  assert property (@(posedge reset) 1 |-> ##0 (out=='0 && selected_input=='0));
  assert property (@cb reset |-> (out=='0 && selected_input=='0));

  // No X/Z on control/output when not in reset
  assert property (@cb !reset |-> !$isunknown(sel));
  assert property (@cb !reset |-> !$isunknown(out));

  // Registered 1-cycle latency: out equals last cycle's selected input (when not coming out of reset)
  assert property (@cb disable iff (reset)
                   !$past(reset) |-> out == $past(pick(sel,in_0,in_1,in_2,in_3)));

  // Out is purely registered (no mid-cycle glitches when not in reset)
  assert property (@(negedge clock) !reset |-> $stable(out));
  // Internal reg also only updates on edges
  assert property (@(negedge clock) !reset |-> $stable(selected_input));

  // Out mirrors internal register
  assert property (@cb out == selected_input);

  // Functional coverage: all selects exercised and each path observed on out
  cover property (@cb !reset && sel==2'b00 ##1 out == $past(in_0));
  cover property (@cb !reset && sel==2'b01 ##1 out == $past(in_1));
  cover property (@cb !reset && sel==2'b10 ##1 out == $past(in_2));
  cover property (@cb !reset && sel==2'b11 ##1 out == $past(in_3));

  // Coverage: reset pulse and subsequent data transfer
  cover property (@(posedge reset) 1 ##1 @cb !reset ##1 out == $past(pick(sel,in_0,in_1,in_2,in_3)));

  // Coverage: back-to-back select changes
  cover property (@cb !reset && sel!= $past(sel) && !$isunknown(sel) && !$isunknown($past(sel)));

endmodule

// Bind into DUT
bind mux4to1 mux4to1_sva #(.W(8)) i_mux4to1_sva (
  .clock(clock),
  .reset(reset),
  .in_0(in_0),
  .in_1(in_1),
  .in_2(in_2),
  .in_3(in_3),
  .sel(sel),
  .out(out),
  .selected_input(selected_input)
);