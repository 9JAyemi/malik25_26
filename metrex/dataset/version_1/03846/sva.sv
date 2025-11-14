// SVA for counter: checks reset behavior, incrementing, wrap-around; includes concise coverage

module counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Reset forces zero on the next cycle
  a_reset_to_zero_next: assert property (reset |=> out == 4'h0);

  // While reset is held across cycles, out stays zero
  a_reset_holds_zero: assert property (reset && $past(reset) |-> out == 4'h0);

  // Increment by 1 mod-16 when not in reset (safe $past default for time 0)
  a_increment_mod16: assert property (disable iff (reset)
                                      out == ($past(out,1,4'h0) + 4'd1));

  // Explicit wrap check from 15 to 0 with reset low
  a_wrap: assert property (disable iff (reset)
                           $past(out) == 4'hF |-> out == 4'h0);

  // Coverage
  c_seen_reset: cover property (reset);
  c_wrap:       cover property (disable iff (reset)
                                $past(out) == 4'hF && out == 4'h0);

  // Optional: one full cycle 0->...->15->0 with no reset
  c_full_cycle: cover property (disable iff (reset)
    out==4'h0 ##1 out==4'h1 ##1 out==4'h2 ##1 out==4'h3 ##1
    out==4'h4 ##1 out==4'h5 ##1 out==4'h6 ##1 out==4'h7 ##1
    out==4'h8 ##1 out==4'h9 ##1 out==4'hA ##1 out==4'hB ##1
    out==4'hC ##1 out==4'hD ##1 out==4'hE ##1 out==4'hF ##1 out==4'h0);
endmodule

bind counter counter_sva counter_sva_i (.clk(clk), .reset(reset), .out(out));