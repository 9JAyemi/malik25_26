// SVA for top_module
// Bind-in assertions; access internal signals directly
module top_module_asserts;

  // Default sampling on clk
  default clocking cb @(posedge clk); endclocking

  // Track valid $past() window (cleared by async reset)
  logic past_valid;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // X/Z checks
  assert property (!$isunknown({reset, slowena, select, a, b}));
  assert property (!reset |-> !$isunknown({out, count, xor_out}));

  // Async reset behavior
  assert property (@(posedge reset) ##0 (count==4'h0 && out==1'b0));
  assert property (reset |-> (count==4'h0 && out==1'b0));

  // XOR correctness
  assert property (xor_out == (a ^ b));

  // Counter behavior
  assert property (disable iff (reset || !past_valid)
                   slowena |=> count == $past(count));
  assert property (disable iff (reset || !past_valid)
                   !slowena |=> count == $past(count)+4'd1);
  assert property (disable iff (reset || !past_valid)
                   ($past(!slowena) && $past(count)==4'hF) |-> (count==4'h0));

  // Registered output select behavior (uses previous-cycle sources)
  assert property (disable iff (reset || !past_valid)
                   $past(select) |-> (out == ($past(a)^$past(b))));
  assert property (disable iff (reset || !past_valid)
                   !$past(select) |-> (out == $past(count[3])));

  // Coverage
  cover property (reset ##1 !reset);
  cover property (disable iff (reset || !past_valid)
                  !slowena ##1 count == $past(count)+4'd1);
  cover property (disable iff (reset || !past_valid)
                  slowena  ##1 count == $past(count));
  cover property (disable iff (reset || !past_valid)
                  $past(select) && out == ($past(a)^$past(b)));
  cover property (disable iff (reset || !past_valid)
                  !$past(select) && out == $past(count[3]));
  cover property (disable iff (reset || !past_valid)
                  $past(!slowena) && $past(count)==4'hF && count==4'h0);

endmodule

bind top_module top_module_asserts tma();