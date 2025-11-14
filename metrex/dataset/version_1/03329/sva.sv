// SVA checker for bcd_to_segment
// Bind this to the DUT: bind bcd_to_segment bcd_to_segment_sva sva_i(.*);

module bcd_to_segment_sva
(
  input logic [3:0] bcd_data,
  input logic [7:0] seg_data
);

  // Fire an event whenever inputs or outputs change
  event ev_bcd_change, ev_any_change;
  always @(bcd_data)                -> ev_bcd_change;
  always @(bcd_data or seg_data)    -> ev_any_change;

  // Golden mapping function (matches DUT)
  function automatic logic [7:0] exp_seg(input logic [3:0] b);
    unique case (b)
      4'h0: exp_seg = 8'hC0;
      4'h1: exp_seg = 8'hF9;
      4'h2: exp_seg = 8'hA4;
      4'h3: exp_seg = 8'hB0;
      4'h4: exp_seg = 8'h99;
      4'h5: exp_seg = 8'h92;
      4'h6: exp_seg = 8'h82;
      4'h7: exp_seg = 8'hF8;
      4'h8: exp_seg = 8'h80;
      4'h9: exp_seg = 8'h90;
      4'hA: exp_seg = 8'h7F; // dp
      default: exp_seg = 8'hFF; // off
    endcase
  endfunction

  // Core functional check: output equals golden mapping (delta-cycle tolerant)
  assert property (@(ev_bcd_change) ##0 seg_data == exp_seg(bcd_data))
    else $error("bcd_to_segment mismatch: bcd=%h seg=%h exp=%h", bcd_data, seg_data, exp_seg(bcd_data));

  // Output should never contain X/Z after a driven update
  assert property (@(ev_bcd_change) ##0 !$isunknown(seg_data))
    else $error("bcd_to_segment produced X/Z: bcd=%h seg=%h", bcd_data, seg_data);

  // Output must not change unless input changes (combinational determinism)
  assert property (@(ev_any_change) $changed(seg_data) |-> $changed(bcd_data))
    else $error("seg_data changed without bcd_data change");

  // Inverse checks for stronger sanity (unique codes)
  assert property (@(ev_any_change) seg_data == 8'hC0 |-> ##0 bcd_data == 4'h0);
  assert property (@(ev_any_change) seg_data == 8'hF9 |-> ##0 bcd_data == 4'h1);
  assert property (@(ev_any_change) seg_data == 8'hA4 |-> ##0 bcd_data == 4'h2);
  assert property (@(ev_any_change) seg_data == 8'hB0 |-> ##0 bcd_data == 4'h3);
  assert property (@(ev_any_change) seg_data == 8'h99 |-> ##0 bcd_data == 4'h4);
  assert property (@(ev_any_change) seg_data == 8'h92 |-> ##0 bcd_data == 4'h5);
  assert property (@(ev_any_change) seg_data == 8'h82 |-> ##0 bcd_data == 4'h6);
  assert property (@(ev_any_change) seg_data == 8'hF8 |-> ##0 bcd_data == 4'h7);
  assert property (@(ev_any_change) seg_data == 8'h80 |-> ##0 bcd_data == 4'h8);
  assert property (@(ev_any_change) seg_data == 8'h90 |-> ##0 bcd_data == 4'h9);
  assert property (@(ev_any_change) seg_data == 8'h7F |-> ##0 bcd_data == 4'hA);
  assert property (@(ev_any_change) seg_data == 8'hFF |-> ##0 (bcd_data inside {[4'hB:4'hF]}));

  // Functional coverage (observe each mapping)
  cover property (@(ev_bcd_change) bcd_data == 4'h0 ##0 seg_data == 8'hC0);
  cover property (@(ev_bcd_change) bcd_data == 4'h1 ##0 seg_data == 8'hF9);
  cover property (@(ev_bcd_change) bcd_data == 4'h2 ##0 seg_data == 8'hA4);
  cover property (@(ev_bcd_change) bcd_data == 4'h3 ##0 seg_data == 8'hB0);
  cover property (@(ev_bcd_change) bcd_data == 4'h4 ##0 seg_data == 8'h99);
  cover property (@(ev_bcd_change) bcd_data == 4'h5 ##0 seg_data == 8'h92);
  cover property (@(ev_bcd_change) bcd_data == 4'h6 ##0 seg_data == 8'h82);
  cover property (@(ev_bcd_change) bcd_data == 4'h7 ##0 seg_data == 8'hF8);
  cover property (@(ev_bcd_change) bcd_data == 4'h8 ##0 seg_data == 8'h80);
  cover property (@(ev_bcd_change) bcd_data == 4'h9 ##0 seg_data == 8'h90);
  cover property (@(ev_bcd_change) bcd_data == 4'hA ##0 seg_data == 8'h7F);
  cover property (@(ev_bcd_change) (bcd_data inside {[4'hB:4'hF]}) ##0 seg_data == 8'hFF);

endmodule