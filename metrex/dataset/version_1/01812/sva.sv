// SVA/coverage for bcd_converter, mux_and_adder, and top_module.
// Concise, quality-focused, bind-ready.

// Checker for bcd_converter
module bcd_converter_sva (
  input logic [3:0] in,
  input logic [3:0] bcd_high,
  input logic [3:0] bcd_low
);
  function automatic logic [3:0] exp_high(input logic [3:0] x);
    exp_high = (x>=4'd5) ? 4'd3 : 4'd0;
  endfunction
  function automatic logic [3:0] exp_low(input logic [3:0] x);
    exp_low = (x>=4'd5) ? (x-4'd5) : x;
  endfunction

  // Invariant checks (combinational)
  always_comb begin
    assert (!$isunknown({in,bcd_high,bcd_low})) else $error("bcd_converter: X/Z detected");
    assert (bcd_high == exp_high(in)) else $error("bcd_converter: bcd_high mismatch");
    assert (bcd_low  == exp_low(in))  else $error("bcd_converter: bcd_low mismatch");
    assert (bcd_high inside {4'd0,4'd3}) else $error("bcd_converter: bcd_high out of set {0,3}");
  end

  // Lightweight functional coverage
  covergroup cg_bcd_conv;
    coverpoint in {
      bins lt5[] = {[0:4]};
      bins ge5[] = {[5:15]};
      bins b0  = {0}; bins b4={4}; bins b5={5}; bins b9={9}; bins b15={15};
    }
    coverpoint bcd_high { bins zero={0}; bins three={3}; illegal_bins others = default; }
    cross in, bcd_high;
  endgroup
  cg_bcd_conv cg = new();
  always @* cg.sample();
endmodule

// Checker for mux_and_adder
module mux_and_adder_sva (
  input  logic [15:0] mux_in,
  input  logic [3:0]  sel,
  input  logic        EN,
  input  logic [3:0]  bcd_high,
  input  logic [3:0]  bcd_low,
  input  logic [3:0]  bcd_sum
);
  logic [3:0] m;
  always_comb begin
    // choose nibble by sel[1:0]
    unique case (sel[1:0])
      2'd0: m = mux_in[3:0];
      2'd1: m = mux_in[7:4];
      2'd2: m = mux_in[11:8];
      2'd3: m = mux_in[15:12];
    endcase

    logic [3:0] exp_sum;
    unique case (sel[3:2])
      2'b00: exp_sum = bcd_low + m;
      2'b01: exp_sum = bcd_high + m;
      2'b10: exp_sum = bcd_low + bcd_high + m;
      default: exp_sum = 4'h0;
    endcase

    assert (!$isunknown({mux_in,sel,EN,bcd_high,bcd_low,bcd_sum})) else $error("mux_and_adder: X/Z detected");
    assert (bcd_sum == exp_sum) else $error("mux_and_adder: bcd_sum mismatch");
  end

  // Coverage: exercise all sel encodings, EN states, and default path
  covergroup cg_mux;
    coverpoint sel { bins all[] = {[0:15]}; bins def = {[12:15]}; }
    coverpoint EN  { bins off={0}; bins on={1}; }
    cross sel, EN;
  endgroup
  cg_mux cg = new();
  always @* cg.sample();
endmodule

// End-to-end checker for top_module
module top_module_sva (
  input  logic [3:0]  in,
  input  logic [15:0] mux_in,
  input  logic [3:0]  sel,
  input  logic        EN,
  input  logic [3:0]  bcd_high,
  input  logic [3:0]  bcd_low
);
  function automatic logic [3:0] conv_hi(input logic [3:0] x);
    conv_hi = (x>=4'd5) ? 4'd3 : 4'd0;
  endfunction
  function automatic logic [3:0] conv_lo(input logic [3:0] x);
    conv_lo = (x>=4'd5) ? (x-4'd5) : x;
  endfunction
  function automatic logic [3:0] sel_nibble(input logic [15:0] din, input logic [1:0] s);
    case (s)
      2'd0: sel_nibble = din[3:0];
      2'd1: sel_nibble = din[7:4];
      2'd2: sel_nibble = din[11:8];
      default: sel_nibble = din[15:12];
    endcase
  endfunction

  // Compute expected end-to-end behavior
  logic [3:0] s1_hi, s1_lo, nib, sum4, exp_hi, exp_lo;
  always_comb begin
    s1_hi = conv_hi(in);
    s1_lo = conv_lo(in);
    nib   = sel_nibble(mux_in, sel[1:0]);
    unique case (sel[3:2])
      2'b00: sum4 = s1_lo + nib;
      2'b01: sum4 = s1_hi + nib;
      2'b10: sum4 = s1_lo + s1_hi + nib;
      default: sum4 = 4'h0;
    endcase
    exp_hi = conv_hi(sum4);
    exp_lo = conv_lo(sum4);

    assert (!$isunknown({in,mux_in,sel,EN,bcd_high,bcd_low})) else $error("top: X/Z detected");
    assert (bcd_high == exp_hi && bcd_low == exp_lo) else $error("top: final BCD mismatch");
  end

  // Minimal end-to-end coverage: branches and groups
  covergroup cg_top;
    coverpoint in { bins lt5={[0:4]}; bins ge5={[5:15]}; }
    coverpoint sel_grp = sel[3:2] { bins g0={2'b00}; bins g1={2'b01}; bins g2={2'b10}; bins g3={2'b11}; }
    cross in, sel_grp;
  endgroup
  cg_top cg = new();
  always @* cg.sample();
endmodule

// Binds
bind bcd_converter   bcd_converter_sva   bcd_converter_sva_i(.*);
bind mux_and_adder   mux_and_adder_sva   mux_and_adder_sva_i(.*);
bind top_module      top_module_sva      top_module_sva_i(.*);