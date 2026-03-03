// SVA for binary_counter
module binary_counter_sva #(parameter WIDTH=4)
(
  input  wire              CLK,
  input  wire              RST,
  input  wire              COUNT_EN,
  input  wire [WIDTH-1:0]  Q
);

  default clocking cb @(posedge CLK); endclocking

  // Sanity: no X/Z on key signals
  a_no_x:         assert property (!$isunknown({RST, COUNT_EN, Q}));

  // Synchronous reset: next cycle must be zero
  a_rst_sync:     assert property (RST |=> Q == '0);

  // Hold when disabled (and not in reset)
  a_hold:         assert property (!RST && !COUNT_EN |=> Q == $past(Q));

  // Increment by 1 mod 2**WIDTH when enabled (and not in reset)
  a_inc:          assert property (!RST && COUNT_EN |=> Q == (($past(Q)+1) % (1<<WIDTH)));

  // Any change must be caused by either reset or enable in prior cycle
  a_change_gated: assert property ((Q != $past(Q)) |-> ($past(RST) || $past(COUNT_EN)));

  // Glitch-free between clocks (output stable away from posedge updates)
  a_no_glitch:    assert property (@(negedge CLK) $stable(Q));

  // Coverage
  c_reset:        cover property (RST |=> Q == '0);
  c_wrap:         cover property (!RST && COUNT_EN && Q == {WIDTH{1'b1}} |=> Q == '0);
  c_inc:          cover property (!RST && COUNT_EN |=> Q == (($past(Q)+1) % (1<<WIDTH)));
  c_en_burst:     cover property (!RST ##1 COUNT_EN[*4]);

endmodule

bind binary_counter binary_counter_sva #(.WIDTH(4)) u_binary_counter_sva (.*);