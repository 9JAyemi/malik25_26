// SVA for mux_4to1_and and its 2:1 sub-muxes.
// Concise, high-quality checks and coverage. Bind these into the DUTs.

// Generic 2:1 mux assertions (binds to every mux2to1 instance)
module mux2to1_sva (
  input logic [3:0] a, b,
  input logic       sel,
  input logic [3:0] y
);
  // Sanity
  assert property (@(a or b or sel or y) !$isunknown(sel));
  assert property (@(a or b or sel or y) !$isunknown(y));

  // Functional equivalence
  assert property (@(a or b or sel or y) y == (sel ? b : a));

  // Coverage: both select paths observed
  cover property (@(a or b or sel or y) (sel==1'b0) && y==a);
  cover property (@(a or b or sel or y) (sel==1'b1) && y==b);
endmodule

bind mux2to1 mux2to1_sva u_mux2to1_sva(.a(a),.b(b),.sel(sel),.y(y));


// Top-level 4:1 mux composition + optional post-AND mask.
// Set MASK_EN=1 if the AND mask 4'b1010 is expected to be applied after final mux.
module mux_4to1_and_sva #(
  parameter bit MASK_EN = 1'b0
) (
  input  logic [3:0] a, b, c, d,
  input  logic [1:0] sel,
  input  logic [3:0] y,
  input  logic [3:0] mux1_out,
  input  logic [3:0] mux2_out
);
  // Derived expectations
  let exp_lo   = sel[0] ? b : a;         // expected mux1_out
  let exp_hi   = sel[0] ? d : c;         // expected mux2_out
  let exp_mux  = sel[1] ? exp_hi : exp_lo;
  let exp_y    = MASK_EN ? (exp_mux & 4'b1010) : exp_mux;

  // Sanity on controls/outputs
  assert property (@(a or b or c or d or sel or y) !$isunknown(sel));
  assert property (@(a or b or c or d or sel or y) !$isunknown(y));

  // Check internal stage correctness
  assert property (@(a or b or sel or mux1_out) mux1_out == exp_lo);
  assert property (@(c or d or sel or mux2_out) mux2_out == exp_hi);

  // Check final output (with optional mask)
  assert property (@(a or b or c or d or sel or y or mux1_out or mux2_out) y == exp_y);

  // If mask is enabled, masked-off bits must be 0
  assert property (@(y) MASK_EN |-> (y[0]==1'b0 && y[2]==1'b0));

  // Functional coverage: all 4 select combinations seen with correct output
  cover property (@(a or b or c or d or sel or y) (sel==2'b00) && (y == (MASK_EN ? (a & 4'b1010) : a)));
  cover property (@(a or b or c or d or sel or y) (sel==2'b01) && (y == (MASK_EN ? (b & 4'b1010) : b)));
  cover property (@(a or b or c or d or sel or y) (sel==2'b10) && (y == (MASK_EN ? (c & 4'b1010) : c)));
  cover property (@(a or b or c or d or sel or y) (sel==2'b11) && (y == (MASK_EN ? (d & 4'b1010) : d)));
endmodule

bind mux_4to1_and mux_4to1_and_sva
  #(.MASK_EN(1'b0))  // set to 1'b1 if the AND mask is intended
  u_mux_4to1_and_sva (
    .a(a), .b(b), .c(c), .d(d),
    .sel(sel), .y(y),
    .mux1_out(mux1_out), .mux2_out(mux2_out)
  );