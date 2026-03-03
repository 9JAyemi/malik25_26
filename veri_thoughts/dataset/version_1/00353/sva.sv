// SVA for bcd_counter, priority_encoder, multiplier, and top_module
// Focused, high-quality checks and compact coverage

// ----------------------------------------
// bcd_counter assertions
module bcd_counter_sva (input clk, input reset, input [3:0] q);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior and next-state relation
  assert property ( $past(reset) |-> (q == 4'd0) );
  assert property ( disable iff (reset)
                    ($past(q) inside {[4'd0:4'd8]}) |-> (q == $past(q)+4'd1) );
  assert property ( disable iff (reset)
                    ($past(q) == 4'd9) |-> (q == 4'd0) );
  assert property ( disable iff (reset)
                    !($past(q) inside {[4'd0:4'd9]}) |-> (q == 4'd0) );

  // Safety: BCD range only
  assert property ( q inside {[4'd0:4'd9]} );

  // Coverage: digits and wrap
  genvar i;
  generate for (i=0; i<=9; i++) begin : CVAL
    cover property ( q == i[3:0] );
  end endgenerate
  cover property ( disable iff (reset) ($past(q)==4'd9) && (q==4'd0) );
endmodule

bind bcd_counter bcd_counter_sva i_bcd_counter_sva (.clk(clk), .reset(reset), .q(q));

// ----------------------------------------
// priority_encoder assertions (clockless, combinational equivalence)
module priority_encoder_sva (input [3:0] in, input [1:0] out);
  // Functional equivalence must always hold on any change
  assert property ( @(in or out)
                    out[1] == (|in[3:2]) && out[0] == (|in[1:0]) );

  // Coverage: all output combinations observable
  cover property ( @(in or out) (in==4'b0000) && (out==2'b00) );
  cover property ( @(in or out) (|in[3:2]) && ~(|in[1:0]) && (out==2'b10) );
  cover property ( @(in or out) ~(|in[3:2]) && (|in[1:0]) && (out==2'b01) );
  cover property ( @(in or out) (|in[3:2]) && (|in[1:0]) && (out==2'b11) );
endmodule

bind priority_encoder priority_encoder_sva i_priority_encoder_sva (.in(in), .out(out));

// ----------------------------------------
// multiplier assertions (clockless, combinational equivalence)
module multiplier_sva (input [3:0] in, input [7:0] out);
  assert property ( @(in or out) out == {in, 4'b0000} );

  // Coverage: a few representative inputs
  cover property ( @(in or out) (in==4'd0)  && (out==8'h00) );
  cover property ( @(in or out) (in==4'd9)  && (out==8'h90) );
  cover property ( @(in or out) (in==4'd15) && (out==8'hF0) );
endmodule

bind multiplier multiplier_sva i_multiplier_sva (.in(in), .out(out));

// ----------------------------------------
// top_module assertions (end-to-end)
module top_module_sva (input clk, input reset, input [3:0] ena, input [7:0] q);
  default clocking cb @(posedge clk); endclocking

  // Post-reset state
  assert property ( $past(reset) |-> (q==8'h00 && ena[1:0]==2'b00 && ena[3:2]==2'b00) );

  // Multiplier relation: lower nibble zero; upper nibble BCD [0:9]
  assert property ( q[3:0] == 4'b0000 );
  assert property ( q[7:4] inside {[4'd0:4'd9]} );

  // Counter next-state mapping via q[7:4]
  assert property ( disable iff (reset)
                    ($past(q[7:4]) inside {[4'd0:4'd8]}) |-> (q[7:4] == $past(q[7:4])+4'd1) );
  assert property ( disable iff (reset)
                    ($past(q[7:4]) == 4'd9) |-> (q[7:4] == 4'd0) );

  // Encoder relation via q[7:4]
  assert property ( ena[3:2] == 2'b00 );
  assert property ( ena[1] == (|q[7:6]) );
  assert property ( ena[0] == (|q[5:4]) );

  // Coverage: key states and transitions
  cover property ( q == 8'h00 );  // 0
  cover property ( q == 8'h50 );  // 5
  cover property ( q == 8'h90 );  // 9
  cover property ( disable iff (reset) ($past(q)==8'h90) && (q==8'h00) ); // wrap 9->0

  // Coverage: all ena combinations reachable
  cover property ( ena == 4'b0000 ); // digit 0
  cover property ( ena == 4'b0001 ); // digits 1..3
  cover property ( ena == 4'b0010 ); // digits 4 or 8
  cover property ( ena == 4'b0011 ); // digits 5..7 or 9
endmodule

bind top_module top_module_sva i_top_module_sva (.clk(clk), .reset(reset), .ena(ena), .q(q));