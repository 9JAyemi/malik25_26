// SVA checker for vga_bsprite
module vga_bsprite_sva
  #(parameter int unsigned hbp = 10'b0010010000,
               int unsigned vbp = 10'b0000011111)
(
  input  logic        vidon,
  input  logic [9:0]  hc,
  input  logic [9:0]  vc,
  input  logic [7:0]  M,
  input  logic [3:0]  posx,
  input  logic [3:0]  posy,
  input  logic [7:0]  face,
  input  logic [9:0]  rom_addr26,
  input  logic [7:0]  rom_addr16,
  input  logic [2:0]  red,
  input  logic [2:0]  green,
  input  logic [1:0]  blue,
  input  logic [3:0]  C1,
  input  logic [3:0]  R1,
  input  logic [3:0]  xpix,
  input  logic [3:0]  ypix,
  input  logic [9:0]  fx,
  input  logic [9:0]  fy,
  input  logic        spriteon,
  input  logic        faceon,
  input  logic [19:0] addrface
);

  // Reference math
  logic signed [11:0] dx, dy, dx_spr, dy_spr, dx_face, dy_face;
  logic               spriteon_ref, faceon_ref;
  logic [3:0]         C1_ref, R1_ref, xpix_ref, ypix_ref;
  logic [19:0]        addrface_calc;

  always_comb begin
    dx       = $signed({1'b0,hc}) - $signed({1'b0,hbp});
    dy       = $signed({1'b0,vc}) - $signed({1'b0,vbp});
    dx_spr   = dx - 12'd240;
    dy_spr   = dy - 12'd200;
    dx_face  = dx - 12'd307;
    dy_face  = dy - 12'd174;
    spriteon_ref = (dx_spr>=0 && dx_spr<12'd160 && dy_spr>=0 && dy_spr<12'd160);
    faceon_ref   = (dx_face>=0 && dx_face<12'd26  && dy_face>=0 && dy_face<12'd26);
    C1_ref   = dx_spr[7:4];
    R1_ref   = dy_spr[7:4];
    xpix_ref = dx_spr[3:0];
    ypix_ref = dy_spr[3:0];
    addrface_calc = (20'd26 * fy) + fx;

    // No Xs on key outputs
    assert (!$isunknown({red,green,blue,rom_addr26,rom_addr16,C1,R1}));

    // spriteon/faceon correctness and mutual exclusion
    assert (spriteon == spriteon_ref);
    assert (faceon   == faceon_ref);
    assert (!(spriteon && faceon));

    // Sprite addressing and bounds when active
    if (spriteon_ref) begin
      assert (C1 == C1_ref);
      assert (R1 == R1_ref);
      assert (xpix == xpix_ref);
      assert (ypix == ypix_ref);
      assert (xpix < 4'd16 && ypix < 4'd16 && C1 < 4'd10 && R1 < 4'd10);
    end
    // rom_addr16 is always {ypix,xpix}
    assert (rom_addr16 == {ypix, xpix});

    // Face addressing
    if (faceon_ref) begin
      assert (fx == dx_face[9:0]);
      assert (fy == dy_face[9:0]);
      assert (fx < 10'd26 && fy < 10'd26);
    end
    // addrface linearization and truncation
    assert (addrface == addrface_calc);
    assert (rom_addr26 == addrface[9:0]);

    // Color rules
    if (!vidon || (!spriteon && !faceon)) begin
      assert (red==3'd0 && green==3'd0 && blue==2'd0);
    end
    if (spriteon && vidon) begin
      if (!(R1==posy && C1==posx)) begin
        assert (red==M[7:5] && green==M[4:2] && blue==M[1:0]);
      end else begin
        assert (green==M[4:2] && blue==M[1:0]);
        if (M[7:5] < 3'd7) assert (red == M[7:5]+3'd1);
        else               assert (red == 3'd7);
      end
    end
    if (!spriteon && faceon && vidon) begin
      assert (red==face[7:5] && green==face[4:2] && blue==face[1:0]);
    end

    // Output ranges
    assert (red <= 3'd7 && green <= 3'd7 && blue <= 2'd3);

    // Covers
    cover (spriteon && vidon && !(R1==posy && C1==posx));
    cover (spriteon && vidon &&  (R1==posy && C1==posx) && M[7:5] != 3'd7);
    cover (spriteon && vidon &&  (R1==posy && C1==posx) && M[7:5] == 3'd7);
    cover (!spriteon && faceon && vidon);
    cover (spriteon && xpix==4'd0  && ypix==4'd0);
    cover (spriteon && xpix==4'd15 && ypix==4'd15);
    cover (faceon && fx==10'd0  && fy==10'd0);
    cover (faceon && fx==10'd25 && fy==10'd25);
  end

endmodule

// Bind into DUT (connects to DUT internals by name)
bind vga_bsprite vga_bsprite_sva sva_vga_bsprite (
  .vidon(vidon),
  .hc(hc),
  .vc(vc),
  .M(M),
  .posx(posx),
  .posy(posy),
  .face(face),
  .rom_addr26(rom_addr26),
  .rom_addr16(rom_addr16),
  .red(red),
  .green(green),
  .blue(blue),
  .C1(C1),
  .R1(R1),
  .xpix(xpix),
  .ypix(ypix),
  .fx(fx),
  .fy(fy),
  .spriteon(spriteon),
  .faceon(faceon),
  .addrface(addrface)
);