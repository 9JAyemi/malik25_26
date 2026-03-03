// SVA checker bound to the DUT
module shift_register_sva (
  input logic        Clock,
  input logic        ALOAD,
  input logic [8:0]  D,
  input logic        SO,
  input logic [8:0]  tmp,
  input logic        n22
);
  default clocking cb @(posedge Clock); endclocking

  // Guard for $past()
  logic past_valid;
  always_ff @(posedge Clock) past_valid <= 1'b1;

  // Sanity: no X on key signals (sampled)
  assert property (disable iff (!past_valid) !$isunknown(ALOAD) && !$isunknown(D[0]));
  assert property (!$isunknown(SO));
  assert property (!$isunknown(n22));

  // Combinational equivalence
  assert property (n22 === (ALOAD & tmp[8]));

  // Sequential next-state checks
  assert property (disable iff (!past_valid) tmp[0] == $past(D[0]));
  genvar i;
  generate
    for (i = 1; i <= 7; i++) begin : g_shifts
      assert property (disable iff (!past_valid) tmp[i] == $past(tmp[i-1]));
      cover  property (disable iff (!past_valid) tmp[i] == $past(tmp[i-1]));
    end
  endgenerate

  // SO and tmp[8] next-state behavior
  assert property (disable iff (!past_valid)
                   SO == ($past(ALOAD) ? $past(D[0]) : $past(tmp[1])));
  assert property (disable iff (!past_valid)
                   tmp[8] == ($past(ALOAD) ? $past(D[0]) : $past(tmp[1])));
  // Optional same-cycle consistency (checked at next clock)
  assert property (disable iff (!past_valid) 1 |-> (tmp[8] == SO));

  // Detect multiple-driver conflict on tmp[8] across the two always blocks
  // If ALOAD=1, both blocks would assign D[0] vs tmp[7]
  // If ALOAD=0, both blocks would assign tmp[1] vs tmp[7]
  assert property (disable iff (!past_valid)
                   ($past(ALOAD)  && ($past(D[0])   == $past(tmp[7]))) ||
                   (!$past(ALOAD) && ($past(tmp[1]) == $past(tmp[7]))))
    else $error("tmp[8] next-state has conflicting drivers (race between always blocks)");

  // Functional coverage of both SO paths
  cover property (disable iff (!past_valid)  ALOAD  && (SO == $past(D[0])));
  cover property (disable iff (!past_valid) !ALOAD && (SO == $past(tmp[1])));
endmodule

// Bind into DUT
bind shift_register shift_register_sva sva_i (.*);