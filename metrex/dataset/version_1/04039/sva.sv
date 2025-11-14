// SVA for counter. Bind or instantiate alongside DUT.

module counter_sva #(
  parameter int WIDTH   = 8,
  parameter int MODULUS = 256
)(
  input  logic                 clk,
  input  logic                 ce,
  input  logic                 clr,
  input  logic [WIDTH-1:0]     out
);

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity
  initial begin
    assert (MODULUS > 0) else $error("MODULUS must be > 0");
    assert (MODULUS <= (1<<WIDTH)) else $error("MODULUS must fit in WIDTH");
  end

  // Clear behavior (dominates ce)
  a_clr_now:  assert property (clr |-> out == '0);
  a_clr_hold: assert property ($rose(clr) |-> (out == '0 throughout clr));

  // Hold when ce=0 (no clr)
  a_hold_no_ce: assert property (($past(1'b1) && !clr && !ce) |-> out == $past(out));

  // Increment / wrap when ce=1 (no clr)
  a_inc_or_wrap: assert property (($past(1'b1) && !clr && ce)
                                  |-> out == (($past(out) == (MODULUS-1)) ? '0 : $past(out)+1));

  // Range invariant
  a_in_range: assert property ((!$isunknown(out)) |-> (out < MODULUS));

  // Periodicity over MODULUS ce-cycles with no clr
  sequence ce_run_modulus; (!clr && ce) [*MODULUS]; endsequence
  a_periodicity: assert property ($past(1'b1, MODULUS) && ce_run_modulus
                                  |=> out == $past(out, MODULUS));

  // Functional coverage
  c_inc3:  cover property (!clr && ce && out==0 ##1 !clr && ce && out==1 ##1 !clr && ce && out==2);
  c_wrap:  cover property ((!clr && ce && out==(MODULUS-1)) |=> (out==0));
  c_clr:   cover property (ce && clr && out==0);
  c_hold:  cover property ((!clr && !ce && $stable(out)) ##1 (!clr && !ce && $stable(out)));

endmodule

// Example bind:
// bind counter counter_sva #(.WIDTH(WIDTH), .MODULUS(MODULUS)) u_counter_sva (.*);