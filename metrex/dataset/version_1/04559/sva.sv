// SVA checker for counter_display
module counter_display_sva (
  input  logic        clk,
  input  logic        reset,       // sync, active-high
  input  logic        direction,
  input  logic [6:0]  seg,
  input  logic [3:0]  cnt,
  input  logic [7:0]  out,
  input  logic        cnt_up,
  input  logic        cnt_down
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  function automatic logic [3:0] inc4(input logic [3:0] a); inc4 = a + 4'd1; endfunction
  function automatic logic [3:0] dec4(input logic [3:0] a); dec4 = a - 4'd1; endfunction

  // Reset behavior
  assert property (@(posedge clk) reset |-> cnt == 4'd0);

  // Count up/down semantics (mod-16)
  assert property ( direction |=> cnt == inc4($past(cnt,1,4'd0)) );
  assert property ( !direction |=> cnt == dec4($past(cnt,1,4'd0)) );

  // Output mapping/invariants
  assert property ( out == {cnt, 4'b0000} );
  assert property ( seg == out[6:0] );
  assert property ( seg[3:0] == 4'b0000 );
  assert property ( {out[7], seg[6:4]} == cnt ); // out[7]=cnt[3], seg[6:4]=cnt[2:0]

  // XOR helpers correctness
  assert property ( cnt_up   == (cnt[0] ^ cnt[1]) );
  assert property ( cnt_down == (cnt[2] ^ cnt[3]) );

  // No X/Z on key signals when not in reset
  assert property ( !$isunknown({cnt, seg, out, cnt_up, cnt_down}) );

  // Coverage
  cover property ( $past(cnt)==4'hF && direction |=> cnt==4'h0 ); // wrap up
  cover property ( $past(cnt)==4'h0 && !direction |=> cnt==4'hF ); // wrap down
  cover property ( direction ##1 !direction );                    // dir change
  cover property ( cnt_up && cnt_down );                          // both XORs = 1
  cover property ( !cnt_up && !cnt_down );                        // both XORs = 0
  cover property ( seg != 7'h00 );                                // non-zero seg pattern seen

endmodule

// Bind into the DUT (connects to internal nets out/cnt_up/cnt_down)
bind counter_display counter_display_sva sva_i (
  .clk      (clk),
  .reset    (reset),
  .direction(direction),
  .seg      (seg),
  .cnt      (cnt),
  .out      (out),
  .cnt_up   (cnt_up),
  .cnt_down (cnt_down)
);