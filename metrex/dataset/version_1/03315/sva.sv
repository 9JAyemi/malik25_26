// Drop this SVA block at the end of acl_fp_ceil, or bind it into the instance.
// Focuses on correctness, gating, pipeline, and corner cases with concise checks.

`ifdef SVA

// ---------- Defaults ----------
default clocking cb @(posedge clock); endclocking
default disable iff (!resetn)

// ---------- Lightweight reference model (I/O only) ----------
function automatic [31:0] ceil32(input [31:0] a);
  automatic bit               s  = a[31];
  automatic logic [7:0]       e  = a[30:23];
  automatic logic [22:0]      m  = a[22:0];
  automatic logic [31:0]      y;
  if (e == 8'hFF) begin
    // NaN / INF pass-through
    y = a;
  end else if (e <= 8'd126) begin
    // |x| < 1
    if (s || (e==0 && m==0)) y = 32'h00000000;     // +0
    else                     y = 32'h3F800000;     // +1.0
  end else begin
    automatic int k  = e - 8'd127; if (k > 23) k = 23;
    automatic int fb = 23 - k; // fractional bits
    automatic bit frac_nz = (fb==0) ? 1'b0 : (|m[0 +: fb]);
    automatic logic [24:0] mp = {1'b0,1'b1,m};
    if (!s && frac_nz) mp = mp + (25'(1) << fb);  // ceil up only if +ve and fractional
    automatic logic [7:0]  eo = e;
    automatic logic [22:0] mo;
    if (mp[24]) begin
      mo = mp[23:1];
      eo = e + 1;
    end else begin
      mo = mp[22:0];
    end
    y = {s, eo, mo};
  end
  return y;
endfunction

// Reference enable-driven 3-stage queue to align with DUT latency
logic [31:0] sva_q0, sva_q1, sva_q2;
int unsigned sva_en_cnt;

always_ff @(posedge clock or negedge resetn) begin
  if (!resetn) begin
    sva_q0 <= '0; sva_q1 <= '0; sva_q2 <= '0;
    sva_en_cnt <= 0;
  end else if (enable) begin
    sva_q0 <= dataa;
    sva_q1 <= sva_q0;
    sva_q2 <= sva_q1;
    if (sva_en_cnt < 3) sva_en_cnt <= sva_en_cnt + 1;
  end
end

// ---------- Basic reset/stability ----------
assert property (!resetn |-> result == 32'd0);

assert property (!enable |=> $stable({
  sign_in, exp_in, man_in,
  sign_1, exp_1, man_1, is_fraction, zero_exponent, addition,
  sign_2, exp_2, man_2,
  sign_3, exp_3, man_3,
  result
}));

// ---------- Stage-0 capture ----------
assert property (enable |=> {sign_in,exp_in,man_in} == {$past(dataa[31]),$past(dataa[30:23]),$past(dataa[22:0])});

// ---------- Stage-1 invariants ----------
assert property (enable |=> man_1[24] == 1'b0);                 // MSB forced 0
assert property (enable |=> man_1[23] == (|$past(exp_in)));     // hidden 1 for normals

// zero_exponent flag semantics
assert property (enable && ($past(exp_in) <= 8'd126) |=> zero_exponent);
assert property (enable && ($past(exp_in) >= 8'd127) |=> !zero_exponent);

// addition value (piecewise compact form)
assert property (enable && ($past(exp_in) <= 8'd126) |=> addition == 25'h0800000);
assert property (enable && ($past(exp_in) >= 8'd127) && ($past(exp_in) <= 8'd150)
                 |=> addition == (25'(1) << (150 - $past(exp_in))));
assert property (enable && ($past(exp_in) > 8'd150) |=> addition == 25'd0);

// is_fraction quick checks
assert property (enable && ($past(exp_in) >= 8'd150) |=> !is_fraction);
assert property (enable && ($past(exp_in) <= 8'd126)
                 |=> is_fraction == ((|$past(man_in)) | (|$past(exp_in))));

// precise is_fraction for 127..149 using variable part-select
assert property (enable && ($past(exp_in) >= 8'd127) && ($past(exp_in) <= 8'd149)
                 |=> is_fraction == (|$past(man_in[0 +: (150 - $past(exp_in))])));

// ---------- Stage-2 behavior ----------
assert property (enable && $past(zero_exponent) |=> sign_2 == 1'b0);

assert property (enable && $past(zero_exponent) && ($past(sign_1) || !$past(is_fraction))
                 |=> (exp_2 == 8'd0) && (man_2 == 25'd0));

assert property (enable && $past(zero_exponent) && (!$past(sign_1) && $past(is_fraction))
                 |=> (exp_2 == 8'd127) && (man_2 == 25'h0800000));

assert property (enable && !$past(zero_exponent)
                 |=> (sign_2 == $past(sign_1)) && (exp_2 == $past(exp_1)));

assert property (enable && !$past(zero_exponent) && $past(is_fraction) && !$past(sign_1)
                 |=> man_2 == ($past(man_1) + $past(addition)));

assert property (enable && (!$past(zero_exponent)) && (!$past(is_fraction) || $past(sign_1))
                 |=> man_2 == $past(man_1));

// ---------- Stage-3 behavior ----------
assert property (enable |=> sign_3 == $past(sign_2));

assert property (enable && $past(man_2[24]) |=> (man_3 == $past(man_2[23:1])) && (exp_3 == ($past(exp_2) + 1'b1)));

assert property (enable && !$past(man_2[24]) && !($past(man_2[23]) && ($past(exp_2)==8'd0))
                 |=> (man_3 == $past(man_2[22:0])) && (exp_3 == $past(exp_2)));

assert property (enable && !$past(man_2[24]) && $past(man_2[23]) && ($past(exp_2)==8'd0)
                 |=> (man_3 == $past(man_2[22:0])) && (exp_3 == 8'd1)); // rare path

// ---------- End-to-end functional check (I/O only, exact latency, handles stalls) ----------
assert property (enable && (sva_en_cnt >= 3) |-> result == ceil32(sva_q2));

// ---------- Corner-case safety ----------
assert property (enable && (exp_2 == 8'hFE) && $past(man_2[24]) |=> exp_3 == 8'hFF); // overflow to INF on +carry
assert property (!$isunknown(result));

// ---------- Targeted coverage ----------
cover property (enable && (dataa[30:23] == 8'd0) && (dataa[31] == 1'b0) && (|dataa[22:0]));          // +subnormal -> +1
cover property (enable && (dataa[30:23] == 8'd0) && (dataa[31] == 1'b1));                              // -subnormal -> +0
cover property (enable && (dataa[30:23] == 8'd127) && (dataa[31] == 1'b0) && (|dataa[22:0]));          // (1,2) +frac -> round up
cover property (enable && (dataa[30:23] == 8'd150) && (dataa[31] == 1'b0) && !(|dataa[22:0]));         // integer, no change
cover property (enable && (dataa[30:23] >  8'd150) && (dataa[31] == 1'b0) && (|dataa[22:0]));          // large +, no frac
cover property (enable && (dataa[30:23] == 8'hFF));                                                     // NaN/INF pass-through
cover property (enable && (exp_2 == 8'hFE) && $past(man_2[24]));                                        // carry-induced overflow

`endif