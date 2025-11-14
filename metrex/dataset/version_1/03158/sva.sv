// Bind these assertions to the DUT. Provide a sampling clock/reset from your TB.
// Example bind:
// bind GenPP_32Bits GenPP_32Bits_sva u_genpp_sva(.clk(clk), .rst_n(rst_n));

module GenPP_32Bits_sva(input logic clk, input logic rst_n);
  localparam int N = 32;

  // Clocking/disable defaults for concise SVA
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Collect DUT outputs into an array for iteration
  wire [N:0] PP [0:15];
  assign PP[0]  = PP0;
  assign PP[1]  = PP1;
  assign PP[2]  = PP2;
  assign PP[3]  = PP3;
  assign PP[4]  = PP4;
  assign PP[5]  = PP5;
  assign PP[6]  = PP6;
  assign PP[7]  = PP7;
  assign PP[8]  = PP8;
  assign PP[9]  = PP9;
  assign PP[10] = PP10;
  assign PP[11] = PP11;
  assign PP[12] = PP12;
  assign PP[13] = PP13;
  assign PP[14] = PP14;
  assign PP[15] = PP15;

  // Helpers: segment extraction, expected Booth value, segment mask
  function automatic logic [2:0] seg_of(int idx, input logic [N-1:0] Y);
    if (idx == 0) seg_of = {Y[1:0], 1'b0};
    else begin
      int hi = 2*idx + 1;
      int lo = 2*idx - 1;
      seg_of = Y[hi : lo];
    end
  endfunction

  function automatic logic [N:0] exp_booth(input logic [2:0] seg, input logic [N-1:0] X);
    unique case (seg)
      3'b000: exp_booth = 33'h0;
      3'b001,
      3'b010: exp_booth = { X[N-1], X };
      3'b011: exp_booth = { X, 1'b0 };
      3'b100: exp_booth = { ~X, 1'b1 };
      3'b101,
      3'b110: exp_booth = { ~X[N-1], ~X };
      3'b111: exp_booth = 33'h1FFFFFFFF;
      default: exp_booth = 'x;
    endcase
  endfunction

  function automatic logic [N-1:0] seg_mask(int idx);
    seg_mask = '0;
    if (idx == 0) begin
      seg_mask[0] = 1'b1;
      seg_mask[1] = 1'b1;
    end else begin
      int b2 = 2*idx+1;
      int b1 = 2*idx;
      int b0 = 2*idx-1;
      seg_mask[b2] = 1'b1;
      seg_mask[b1] = 1'b1;
      seg_mask[b0] = 1'b1;
    end
  endfunction

  function automatic logic any_seg_is(input logic [2:0] code, input logic [N-1:0] Y);
    any_seg_is = 1'b0;
    for (int j=0; j<16; j++) any_seg_is |= (seg_of(j, Y) == code);
  endfunction

  // Core functional equivalence: each PP equals BoothDecode(segment_i, iso_X)
  generate
    for (genvar i=0; i<16; i++) begin : g_eq
      assert property (PP[i] == exp_booth(seg_of(i, iso_Y), iso_X))
        else $error("PP[%0d] mismatch: seg=%b X=%h PP=%h exp=%h",
                    i, seg_of(i, iso_Y), iso_X, PP[i], exp_booth(seg_of(i, iso_Y), iso_X));
    end
  endgenerate

  // Outputs do not depend on iso_in
  assert property (($changed(iso_in) && $stable(iso_X) && $stable(iso_Y)) |-> $stable({PP15,PP14,PP13,PP12,PP11,PP10,PP9,PP8,PP7,PP6,PP5,PP4,PP3,PP2,PP1,PP0}));

  // No X/Z propagation: known inputs imply known outputs
  assert property ((!$isunknown(iso_X) && !$isunknown(iso_Y)) |-> !$isunknown({PP15,PP14,PP13,PP12,PP11,PP10,PP9,PP8,PP7,PP6,PP5,PP4,PP3,PP2,PP1,PP0}));

  // Locality: PP[i] only depends on its own 3-bit segment of Y (X stable)
  generate
    for (genvar i=0; i<16; i++) begin : g_local
      assert property ($stable(iso_X) &&
                       (((iso_Y ^ $past(iso_Y)) & seg_mask(i)) == '0) &&
                       (iso_Y != $past(iso_Y))
                       |-> $stable(PP[i]))
        else $error("PP[%0d] changed due to unrelated Y bits", i);
    end
  endgenerate

  // Sanity: if iso_Y==0, all partial products are zero
  assert property ((iso_Y == '0) |-> ({PP15,PP14,PP13,PP12,PP11,PP10,PP9,PP8,PP7,PP6,PP5,PP4,PP3,PP2,PP1,PP0} == '0));

  // Coverage: exercise all Booth segment codes somewhere across the 16 segments
  cover property (any_seg_is(3'b000, iso_Y));
  cover property (any_seg_is(3'b001, iso_Y));
  cover property (any_seg_is(3'b010, iso_Y));
  cover property (any_seg_is(3'b011, iso_Y));
  cover property (any_seg_is(3'b100, iso_Y));
  cover property (any_seg_is(3'b101, iso_Y));
  cover property (any_seg_is(3'b110, iso_Y));
  cover property (any_seg_is(3'b111, iso_Y));

  // Coverage: X sign bit both 0 and 1
  cover property (iso_X[N-1] == 1'b0);
  cover property (iso_X[N-1] == 1'b1);

  // Coverage: iso_in toggling while data stable (independence)
  cover property ($changed(iso_in) && $stable(iso_X) && $stable(iso_Y));
endmodule