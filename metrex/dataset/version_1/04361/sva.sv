// SVA for binary_counter
module binary_counter_sva #(parameter int W=4)(
  input logic clk,
  input logic rst,
  input logic en,
  input logic [W-1:0] count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  localparam logic [W-1:0] MASK = '1;

  // Sanity: no X on control; count never X when not in reset
  a_no_x_inputs: assert property (!$isunknown({rst,en}));
  a_no_x_count:  assert property (rst || !$isunknown(count));

  // Reset behavior
  a_reset_next_is_zero: assert property (rst |=> count == '0);
  a_reset_hold_zero:    assert property ($past(rst,1,0) |-> count == '0);

  // Functional behavior
  a_inc_when_en: assert property (
    !$past(rst,1,0) && $past(en,1,0)
    |-> count == (($past(count,1,'0) + 1) & MASK)
  );

  a_hold_when_dis: assert property (
    !$past(rst,1,0) && !$past(en,1,0)
    |-> count == $past(count,1,'0)
  );

  // Explicit wrap check
  a_wrap: assert property (
    !$past(rst,1,0) && $past(en,1,0) && $past(count,1,'0) == MASK
    |-> count == '0
  );

  // Any count change must be caused by rst or en
  a_change_has_cause: assert property (
    $changed(count) |-> $past(rst,1,0) || $past(en,1,0)
  );

  // Coverage
  c_reset: cover property (rst ##1 count == '0);
  c_inc:   cover property (!$past(rst,1,0) && $past(en,1,0)
                           ##1 count == (($past(count,1,'0)+1) & MASK));
  c_hold:  cover property (!$past(rst,1,0) && !$past(en,1,0)
                           ##1 count == $past(count,1,'0));
  c_wrap:  cover property (!$past(rst,1,0) && $past(en,1,0) && $past(count,1,'0)==MASK
                           ##1 count == '0);
endmodule

// Bind into DUT
bind binary_counter binary_counter_sva #(.W(4))
  binary_counter_sva_i (.clk(clk), .rst(rst), .en(en), .count(count));