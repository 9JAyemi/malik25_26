// SVA for mult_input
// Concise, bindable, and focused on functional correctness, X-checks, and key coverage.

module mult_input_sva (
  input logic [31:0] in1,
  input logic [31:0] in2,
  input logic [31:0] in3,
  input logic [31:0] in4,
  input logic [31:0] in5,
  input logic [31:0] out
);
  default clocking cb @(*); endclocking

  // 32-bit modular multiply (keeps only low 32 bits each step)
  function automatic logic [31:0] mul32_mod(input logic [31:0] a, b);
    logic [63:0] t;
    t = $unsigned(a) * $unsigned(b);
    return t[31:0];
  endfunction

  function automatic logic [31:0] mul32_5(
    input logic [31:0] a,b,c,d,e
  );
    logic [31:0] r;
    r = mul32_mod(a,b);
    r = mul32_mod(r,c);
    r = mul32_mod(r,d);
    r = mul32_mod(r,e);
    return r;
  endfunction

  function automatic bit mul32_5_overflow(
    input logic [31:0] a,b,c,d,e
  );
    logic [63:0] t;
    logic [31:0] r;
    mul32_5_overflow = 0;
    t = $unsigned(a) * $unsigned(b); mul32_5_overflow |= |t[63:32]; r = t[31:0];
    t = $unsigned(r) * $unsigned(c); mul32_5_overflow |= |t[63:32]; r = t[31:0];
    t = $unsigned(r) * $unsigned(d); mul32_5_overflow |= |t[63:32]; r = t[31:0];
    t = $unsigned(r) * $unsigned(e); mul32_5_overflow |= |t[63:32];
  endfunction

  // Core functional check (unsigned semantics, modulo 2^32)
  a_func: assert property (
    !$isunknown({in1,in2,in3,in4,in5}) |-> out == mul32_5(in1,in2,in3,in4,in5)
  );

  // Out must be known when inputs are known
  a_known: assert property (
    !$isunknown({in1,in2,in3,in4,in5}) |-> !$isunknown(out)
  );

  // Key coverage
  c_zero_factor:      cover property (!$isunknown({in1,in2,in3,in4,in5}) && (in1==0 || in2==0 || in3==0 || in4==0 || in5==0));
  c_one_factor:       cover property (!$isunknown({in1,in2,in3,in4,in5}) && (in1==32'd1 || in2==32'd1 || in3==32'd1 || in4==32'd1 || in5==32'd1));
  c_overflow:         cover property (!$isunknown({in1,in2,in3,in4,in5}) &&  mul32_5_overflow(in1,in2,in3,in4,in5));
  c_no_overflow:      cover property (!$isunknown({in1,in2,in3,in4,in5}) && !mul32_5_overflow(in1,in2,in3,in4,in5));
  c_wrap_to_zero:     cover property (!$isunknown({in1,in2,in3,in4,in5}) && out==32'd0 && (in1!=0 && in2!=0 && in3!=0 && in4!=0 && in5!=0));
  c_all_max:          cover property (!$isunknown({in1,in2,in3,in4,in5}) &&
                                      in1==32'hFFFF_FFFF && in2==32'hFFFF_FFFF &&
                                      in3==32'hFFFF_FFFF && in4==32'hFFFF_FFFF &&
                                      in5==32'hFFFF_FFFF);
endmodule

// Bind into the DUT
bind mult_input mult_input_sva sva (.*);