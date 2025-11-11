// SVA bind module for io_mux
module io_mux_sva #(parameter WIDTH=8) (
  input  [WIDTH-1:0] a_din,
  input  [WIDTH-1:0] a_dout,
  input  [WIDTH-1:0] a_dout_en,
  input  [WIDTH-1:0] b_din,
  input  [WIDTH-1:0] b_dout,
  input  [WIDTH-1:0] b_dout_en,
  input  [WIDTH-1:0] io_din,
  input  [WIDTH-1:0] io_dout,
  input  [WIDTH-1:0] io_dout_en,
  input  [WIDTH-1:0] sel
);

  // Core mux correctness (bitwise)
  // Use case-equality for structural equivalence; X checks are below
  assert property (@*) a_din      === (io_din & ~sel);
  assert property (@*) b_din      === (io_din &  sel);
  assert property (@*) io_dout    === ((~sel & a_dout)    | (sel & b_dout));
  assert property (@*) io_dout_en === ((~sel & a_dout_en) | (sel & b_dout_en));

  // Sanity relationships on io_din fanout
  assert property (@*) ((a_din | b_din) === io_din) && ((a_din & b_din) === '0);

  // X-propagation guards: if inputs known, outputs must be known
  assert property (@*) (!$isunknown({io_din, sel}))            |-> !$isunknown({a_din, b_din});
  assert property (@*) (!$isunknown({a_dout, b_dout, sel}))    |-> !$isunknown(io_dout);
  assert property (@*) (!$isunknown({a_dout_en, b_dout_en, sel})) |-> !$isunknown(io_dout_en);

  // Per-bit coverage to ensure both mux legs are exercised
  genvar i;
  generate
    for (i = 0; i < WIDTH; i++) begin : g_cov
      // Cover both select edges
      cover property (@(posedge  sel[i])) 1;
      cover property (@(negedge  sel[i])) 1;

      // Cover data path selection when sources differ
      cover property (@(posedge sel[i]))  (a_dout[i] !== b_dout[i]) && (io_dout[i] == b_dout[i]);
      cover property (@(negedge sel[i]))  (a_dout[i] !== b_dout[i]) && (io_dout[i] == a_dout[i]);

      // Cover enable path selection when sources differ
      cover property (@(posedge sel[i]))  (a_dout_en[i] !== b_dout_en[i]) && (io_dout_en[i] == b_dout_en[i]);
      cover property (@(negedge sel[i]))  (a_dout_en[i] !== b_dout_en[i]) && (io_dout_en[i] == a_dout_en[i]);

      // Cover io_din routing to the selected destination
      cover property (@(posedge sel[i]))  io_din[i] &&  b_din[i] && !a_din[i];
      cover property (@(negedge sel[i]))  io_din[i] &&  a_din[i] && !b_din[i];
    end
  endgenerate

endmodule

// Bind into the DUT
bind io_mux io_mux_sva #(.WIDTH(WIDTH)) io_mux_sva_b (.*);