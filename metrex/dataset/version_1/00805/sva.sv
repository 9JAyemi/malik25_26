// SVA checkers (bind to DUTs). Focused, comprehensive, and concise.

module priority_encoder_sva(input logic [7:0] in, input logic [2:0] pos);

  // Golden model for priority (LSB has highest priority, 0 if none)
  function automatic logic [2:0] pe_expect(input logic [7:0] vi);
    pe_expect = 3'd0;
    if      (vi[0]) pe_expect = 3'd0;
    else if (vi[1]) pe_expect = 3'd1;
    else if (vi[2]) pe_expect = 3'd2;
    else if (vi[3]) pe_expect = 3'd3;
    else if (vi[4]) pe_expect = 3'd4;
    else if (vi[5]) pe_expect = 3'd5;
    else if (vi[6]) pe_expect = 3'd6;
    else if (vi[7]) pe_expect = 3'd7;
    else            pe_expect = 3'd0;
  endfunction

  // Core correctness
  always_comb begin
    assert (pos === pe_expect(in))
      else $error("priority_encoder mismatch: in=%b pos=%0d exp=%0d", in, pos, pe_expect(in));
    if (~|in) assert (pos === 3'd0)
      else $error("priority_encoder idle case: in=0 expects pos=0, got %0d", pos);
  end

  // Priority-specific implications (concise)
  always_comb begin
    if (in[0])                     assert (pos === 3'd0);
    if (!in[0] && in[1])           assert (pos === 3'd1);
    if (!(|in[1:0]) && in[2])      assert (pos === 3'd2);
    if (!(|in[2:0]) && in[3])      assert (pos === 3'd3);
    if (!(|in[3:0]) && in[4])      assert (pos === 3'd4);
    if (!(|in[4:0]) && in[5])      assert (pos === 3'd5);
    if (!(|in[5:0]) && in[6])      assert (pos === 3'd6);
    if (!(|in[6:0]) && in[7])      assert (pos === 3'd7);
  end

  // X-safety: if inputs are known, output must be known
  always_comb begin
    if (!$isunknown(in)) assert (!$isunknown(pos))
      else $error("priority_encoder produced X/Z pos for known in=%b", in);
  end

  // Coverage: all priorities + multiple-bit priority behavior
  always_comb begin
    cover (~|in && pos==3'd0);
    cover (in==8'b0000_0001 && pos==3'd0);
    cover (in==8'b0000_0010 && pos==3'd1);
    cover (in==8'b0000_0100 && pos==3'd2);
    cover (in==8'b0000_1000 && pos==3'd3);
    cover (in==8'b0001_0000 && pos==3'd4);
    cover (in==8'b0010_0000 && pos==3'd5);
    cover (in==8'b0100_0000 && pos==3'd6);
    cover (in==8'b1000_0000 && pos==3'd7);
    cover (in[7] && in[0] && pos==3'd0); // priority over higher bit
    cover (in[6] && !in[0] && in[3] && pos==3'd3);
  end

endmodule


module multiplexer_sva(
  input logic [3:0] a, b, c, d,
  input logic [1:0] sel,
  input logic [3:0] y
);

  // Golden model for implemented mapping:
  // sel: 00->b, 01->d, 10->c, 11->a
  function automatic logic [3:0] mux_expect(
    input logic [3:0] ia, ib, ic, id,
    input logic [1:0] isel
  );
    unique case (isel)
      2'b00: mux_expect = ib;
      2'b01: mux_expect = id;
      2'b10: mux_expect = ic;
      2'b11: mux_expect = ia;
      default: mux_expect = 'x;
    endcase
  endfunction

  // Core correctness
  always_comb begin
    if (!$isunknown(sel)) begin
      assert (y === mux_expect(a,b,c,d,sel))
        else $error("mux mismatch: sel=%b a=%h b=%h c=%h d=%h y=%h exp=%h",
                    sel, a, b, c, d, y, mux_expect(a,b,c,d,sel));
    end
  end

  // X-safety: when select and selected input are known, y must be known and equal
  always_comb begin
    if (!$isunknown(sel)) begin
      unique case (sel)
        2'b00: if (!$isunknown(b)) assert (y === b);
        2'b01: if (!$isunknown(d)) assert (y === d);
        2'b10: if (!$isunknown(c)) assert (y === c);
        2'b11: if (!$isunknown(a)) assert (y === a);
      endcase
    end
  end

  // Coverage: all select paths
  always_comb begin
    cover (sel==2'b00 && y===b);
    cover (sel==2'b01 && y===d);
    cover (sel==2'b10 && y===c);
    cover (sel==2'b11 && y===a);
  end

endmodule


// Bind checkers to DUTs (type-based)
bind priority_encoder priority_encoder_sva pe_chk(.in(in), .pos(pos));
bind multiplexer     multiplexer_sva     mux_chk(.a(a), .b(b), .c(c), .d(d), .sel(sel), .y(y));