// SVA binders for top_module, johnson_counter, xor_module

// johnson_counter assertions
module jc_sva (input clk, input reset, input [3:0] q);
  default clocking cb @(posedge clk); endclocking

  // Async active-low reset forces zero
  assert property (@(negedge reset) q == 4'b0000);
  assert property (@(posedge clk) !reset |-> q == 4'b0000);

  // Legal state set
  assert property (@(posedge clk)
                   q inside {4'b0000,4'b1000,4'b1100,4'b1110,
                             4'b1111,4'b0111,4'b0011,4'b0001});

  // Next-state mapping when out of reset for two consecutive cycles
  assert property (@(posedge clk) reset && $past(reset) |->
                   (($past(q)==4'b0000) ? (q==4'b1000) :
                    ($past(q)==4'b1000) ? (q==4'b1100) :
                    ($past(q)==4'b1100) ? (q==4'b1110) :
                    ($past(q)==4'b1110) ? (q==4'b1111) :
                    ($past(q)==4'b1111) ? (q==4'b0111) :
                    ($past(q)==4'b0111) ? (q==4'b0011) :
                    ($past(q)==4'b0011) ? (q==4'b0001) :
                    ($past(q)==4'b0001) ? (q==4'b0000) : 1'b1));

  // Coverage: see a full 8-step cycle when released
  cover property (@(posedge clk) reset && $past(reset)
                  ##1 (q==4'b0000) ##1 (q==4'b1000) ##1 (q==4'b1100) ##1 (q==4'b1110)
                  ##1 (q==4'b1111) ##1 (q==4'b0111) ##1 (q==4'b0011) ##1 (q==4'b0001) ##1 (q==4'b0000));
endmodule
bind johnson_counter jc_sva u_jc_sva (.clk(clk), .reset(reset), .q(q));

// xor_module assertions
module xm_sva (input [7:0] in1, input [3:0] in2, input [7:0] out);
  function automatic [7:0] mask_for(input [3:0] s);
    case (s)
      4'b0000: mask_for = 8'h00;
      4'b1000: mask_for = 8'h08;
      4'b1100: mask_for = 8'h0C;
      4'b1110: mask_for = 8'h0E;
      4'b1111: mask_for = 8'h0F;
      4'b0111: mask_for = 8'h07;
      4'b0011: mask_for = 8'h03;
      4'b0001: mask_for = 8'h01;
      default: mask_for = 8'hxx;
    endcase
  endfunction

  // Only legal Johnson states expected on in2
  assert property (@(*) in2 inside {4'b0000,4'b1000,4'b1100,4'b1110,
                                    4'b1111,4'b0111,4'b0011,4'b0001});

  // Truth table
  assert property (@(*) out == (in1 ^ mask_for(in2)));

  // Coverage: hit each in2 code
  cover property (@(*) in2==4'b0000);
  cover property (@(*) in2==4'b1000);
  cover property (@(*) in2==4'b1100);
  cover property (@(*) in2==4'b1110);
  cover property (@(*) in2==4'b1111);
  cover property (@(*) in2==4'b0111);
  cover property (@(*) in2==4'b0011);
  cover property (@(*) in2==4'b0001);
endmodule
bind xor_module xm_sva u_xm_sva (.in1(in1), .in2(in2), .out(out));

// top_module assertions
module top_sva (
  input clk, input reset,
  input [7:0] d,
  input [7:0] q, input [7:0] xor_out,
  input [3:0] johnson_out,
  input [7:0] shift_reg
);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset and update behavior of shift_reg as coded
  assert property (reset |-> shift_reg == 8'h34);
  assert property (!reset |-> shift_reg == $past(d));

  // Structural connectivity
  assert property (@(posedge clk) q == xor_out);

  // Integration: active-low reset into JC implies johnson_out=0 when top reset deasserted
  assert property (@(posedge clk) !reset |-> johnson_out == 4'b0000);

  // No X on key registers/outputs at clock edge
  assert property (@(posedge clk) !$isunknown(shift_reg));
  assert property (@(posedge clk) !$isunknown(q) && !$isunknown(xor_out));

  // Coverage
  cover property (@(posedge clk) reset ##1 !reset);               // reset pulse
  cover property (@(posedge clk) !reset [*8]);                    // run for 8 cycles
  cover property (@(posedge clk) johnson_out==4'b0000);
  cover property (@(posedge clk) johnson_out==4'b1000);
  cover property (@(posedge clk) johnson_out==4'b1100);
  cover property (@(posedge clk) johnson_out==4'b1110);
  cover property (@(posedge clk) johnson_out==4'b1111);
  cover property (@(posedge clk) johnson_out==4'b0111);
  cover property (@(posedge clk) johnson_out==4'b0011);
  cover property (@(posedge clk) johnson_out==4'b0001);
endmodule
bind top_module top_sva u_top_sva (.clk(clk), .reset(reset), .d(d),
                                   .q(q), .xor_out(xor_out), .johnson_out(johnson_out),
                                   .shift_reg(shift_reg));