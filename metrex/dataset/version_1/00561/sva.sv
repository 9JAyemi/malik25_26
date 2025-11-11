// SVA binder for add_sub_module
module add_sub_module_sva #(parameter WIDTH = 32) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  input  logic             sub,
  input  logic [WIDTH-1:0] sum,
  // internal DUT nets (bound hierarchically)
  input  logic [WIDTH-1:0] carry,
  input  logic [WIDTH-1:0] diff
);

  function automatic logic [WIDTH-1:0] model_sum(input logic [WIDTH-1:0] aa,
                                                 input logic [WIDTH-1:0] bb,
                                                 input logic             s);
    return s ? (aa - bb) : (aa + bb);
  endfunction

  // Knownness checks gated by known inputs
  always_comb begin
    if (!$isunknown({a,b,sub})) begin
      assert (!$isunknown(sum)) else $error("sum has X/Z with known inputs");
      assert (!$isunknown({carry[0],diff[0]})) else $error("carry[0]/diff[0] has X/Z with known inputs");
      assert (!$isunknown({carry[WIDTH-1:1]})) else $error("carry bus has X/Z with known inputs");
    end
  end

  // Functional correctness (spec): sum must match add/sub modulo 2^WIDTH
  always_comb begin
    if (!$isunknown({a,b,sub}))
      assert (sum == model_sum(a,b,sub))
        else $error("Spec mismatch: sub=%0b a=%h b=%h sum=%h exp=%h",
                    sub, a, b, sum, model_sum(a,b,sub));
  end

  // Structural/ripple checks (bits 1..WIDTH-1 use full_adder behavior)
  genvar i;
  generate
    for (i=1; i<WIDTH; i++) begin : g_chk
      always_comb begin
        if (!$isunknown({a[i],b[i],carry[i-1]})) begin
          assert (sum[i]   == (a[i] ^ b[i] ^ carry[i-1]))
            else $error("Bit%0d sum mismatch", i);
          assert (carry[i] == ((a[i]&b[i]) | (a[i]&carry[i-1]) | (b[i]&carry[i-1])))
            else $error("Bit%0d carry mismatch", i);
        end
      end
    end
  endgenerate

  // LSB path as implemented in DUT (to catch X/connection issues)
  always_comb begin
    if (!$isunknown({b[0],sub})) begin
      assert (carry[0] == (sub ? ~b[0] : b[0])) else $error("carry[0] compute mismatch");
      assert (diff[0]  == (sub ?  b[0] : ~b[0])) else $error("diff[0] compute mismatch");
    end
    if (!$isunknown({a[0],carry[0],diff[0],sub}))
      assert (sum[0] == (sub ? (a[0]^diff[0]) : (a[0]^carry[0])))
        else $error("LSB sum path mismatch");
  end

  // Lightweight coverage (procedural cover)
  always_comb begin
    cover (sub==0);
    cover (sub==1);
    cover (!sub && (a=={WIDTH{1'b0}}) && (b=={WIDTH{1'b0}}));           // zero+zero
    cover (!sub && (&a) && (&b));                                       // many carries
    cover (!sub && ((a + b) < a));                                      // unsigned overflow
    cover ( sub && (a==b));                                             // zero result on subtract
    cover ( sub && (a < b));                                            // unsigned borrow/underflow
    cover (!sub && (a=={WIDTH{1'b1}}) && (b=={{(WIDTH-1){1'b0}},1'b1}));// ripple carry through all ones
    cover ( sub && (a=={WIDTH{1'b0}}) && (b=={{(WIDTH-1){1'b0}},1'b1}));// ripple borrow
  end

endmodule

// Bind into the DUT; explicit connections include internal nets carry/diff
bind add_sub_module add_sub_module_sva #(.WIDTH(32)) add_sub_module_sva_i (
  .a(a),
  .b(b),
  .sub(sub),
  .sum(sum),
  .carry(carry),
  .diff(diff)
);