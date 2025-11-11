// SVA for DelayBlock: bindable, concise, and checking key behavior
module DelayBlock_sva #(
  parameter int delay = 5
) (
  input  logic                 clk,
  input  logic                 in,
  input  logic                 out,
  input  logic [delay-1:0]     shift_reg
);

  default clocking cb @(posedge clk); endclocking

  // Parameter/sizing sanity
  initial assert (delay >= 2)
    else $fatal(1, "DelayBlock: parameter 'delay' must be >= 2");

  // Simple cycle counter to gate $past usage
  logic [$clog2(delay+1):0] cyc_cnt = '0;
  always_ff @(posedge clk) cyc_cnt <= cyc_cnt + 1'b1;
  wire hist_ready = (cyc_cnt >= delay);

  // No-X check on key signals
  assert property (!$isunknown({in, out, shift_reg})));

  // out must mirror LSB of shift_reg (as coded)
  assert property (out == shift_reg[0]);

  // Shift behavior checks
  genvar k;
  for (k = 0; k < delay; k++) begin : g_shift_checks
    if (k == 0) begin
      assert property (cyc_cnt > 0 |-> shift_reg[0] == $past(in));
    end else begin
      assert property (cyc_cnt > k |-> shift_reg[k] == $past(shift_reg[k-1]));
    end
  end

  // Whole-register update matches concatenation
  if (delay >= 2) begin
    assert property (cyc_cnt > 0 |-> shift_reg == {$past(shift_reg[delay-2:0]), $past(in)});
  end

  // Functional spec: out equals in delayed by 'delay' cycles (will flag current bug)
  assert property (hist_ready |-> out == $past(in, delay));

  // Functional coverage: observe both polarities propagate through the delay
  cover property ($rose(in) ##delay out);
  cover property ($fell(in) ##delay !out);

endmodule

// Bind SVA to the DUT
bind DelayBlock DelayBlock_sva #(.delay(delay)) u_DelayBlock_sva (
  .clk       (clk),
  .in        (in),
  .out       (out),
  .shift_reg (shift_reg)
);