// SVA checkers and binds for edge_detection, bitwise_or, and top_module

// Edge detection checker
module edge_detection_sva #(parameter W=4)
(
  input logic              clk,
  input logic              reset,
  input logic [W-1:0]      in,
  input logic [W-1:0]      out,
  input logic [W-1:0]      prev_in
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Synchronous reset drives prev_in/out to 0 (post-NBA)
  a_reset_zero: assert property (reset |-> ##0 (prev_in=='0 && out=='0));

  // prev_in captures current in each cycle (post-NBA)
  a_prev_update: assert property (1'b1 |-> ##0 (prev_in == in));

  // out pulses where in toggles vs previous cycle (guard first cycle after reset)
  a_out_equiv: assert property ($past(!reset) |-> ##0 (out == (in ^ $past(in))));

  // Coverage: any toggle produces non-zero out
  c_any_toggle: cover property ($past(!reset) && ((in ^ $past(in))!='0) |-> ##0 (out!='0));

  // Coverage: rising and falling edges per bit produce a pulse
  genvar i;
  generate for (i=0; i<W; i++) begin : gen_cov_bits
    c_rise: cover property ($rose(in[i]) |-> ##0 out[i]);
    c_fall: cover property ($fell(in[i]) |-> ##0 out[i]);
  end endgenerate

  // Coverage: multiple bits toggling simultaneously propagate
  c_multi: cover property ($past(!reset) && ($countones(in ^ $past(in))>=2) |-> ##0 ($countones(out)>=2));
endmodule

// Bitwise OR checker
module bitwise_or_sva #(parameter W=4)
(
  input logic [W-1:0] in1,
  input logic [W-1:0] in2,
  input logic [W-1:0] out
);
  // Pure combinational functionality
  a_or_func: assert property (@(in1 or in2 or out) out == (in1 | in2));

  // Coverage: any driven 1 on inputs produces non-zero out
  c_or_act: cover property (@(in1 or in2) (in1|in2)!='0);
endmodule

// Top-level end-to-end checker
module top_module_sva #(parameter W=4)
(
  input logic              clk,
  input logic              reset,
  input logic [W-1:0]      in1,
  input logic [W-1:0]      in2,
  input logic [W-1:0]      out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // End-to-end: OR of per-source edge pulses
  a_e2e: assert property ($past(!reset) |-> ##0 (out == ((in1 ^ $past(in1)) | (in2 ^ $past(in2)))));

  // Coverage: simultaneous edges from both sources contribute
  c_both: cover property ($past(!reset) &&
                          ((in1 ^ $past(in1))!='0) && ((in2 ^ $past(in2))!='0)
                          |-> ##0 (out!='0));
endmodule

// Bind the checkers
bind edge_detection edge_detection_sva #(.W(4)) ed_chk (.clk(clk), .reset(reset), .in(in), .out(out), .prev_in(prev_in));
bind bitwise_or     bitwise_or_sva     #(.W(4)) or_chk (.in1(in1), .in2(in2), .out(out));
bind top_module     top_module_sva     #(.W(4)) top_chk (.clk(clk), .reset(reset), .in1(in1), .in2(in2), .out(out));