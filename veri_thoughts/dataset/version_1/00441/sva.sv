// SVA checker + bind for binary_multiplier
bind binary_multiplier binary_multiplier_sva i_binary_multiplier_sva (.a(a), .b(b), .result(result), .temp(temp));

module binary_multiplier_sva (
  input logic [7:0]   a,
  input logic [7:0]   b,
  input logic [15:0]  result,
  input logic [15:0]  temp
);

  // Core functional checks and X-prop (combinational)
  always_comb begin
    if (!$isunknown({a,b})) begin
      assert (result == a*b)
        else $error("binary_multiplier: result != a*b (a=%0d b=%0d res=%0d exp=%0d)", a, b, result, a*b);
      assert (!$isunknown(result))
        else $error("binary_multiplier: result X/Z with known inputs");
    end
    assert (result === temp)
      else $error("binary_multiplier: result != temp");
    if (a==0 || b==0)  assert (result==0)
      else $error("binary_multiplier: zero-multiplicand property failed");
    if (a==8'd1)       assert (result==b)
      else $error("binary_multiplier: identity a*1 failed");
    if (b==8'd1)       assert (result==a)
      else $error("binary_multiplier: identity 1*b failed");
    assert (result == b*a)
      else $error("binary_multiplier: commutativity failed");

    // Lightweight scenario coverage
    cover (a==0 && b==0);
    cover (a==0 && b!=0);
    cover (a!=0 && b==0);
    cover (a==8'd1);
    cover (b==8'd1);
    cover (a==8'hFF && b==8'hFF);
    cover (result[15:8] != 0); // overflow into upper byte
  end

  // No output change without input change (combinational sanity)
  always @(result) begin
    assert ($changed(a) || $changed(b))
      else $error("binary_multiplier: result changed without input change");
  end

  // Functional coverage (sample on input changes)
  covergroup mult_cg;
    option.per_instance = 1;
    a_cp: coverpoint a {
      bins zero = {8'd0};
      bins one  = {8'd1};
      bins max  = {8'hFF};
      bins pow2[] = {8'd1,8'd2,8'd4,8'd8,8'd16,8'd32,8'd64,8'd128};
    }
    b_cp: coverpoint b {
      bins zero = {8'd0};
      bins one  = {8'd1};
      bins max  = {8'hFF};
      bins pow2[] = {8'd1,8'd2,8'd4,8'd8,8'd16,8'd32,8'd64,8'd128};
    }
    ovf_cp: coverpoint result[15:8] {
      bins no_ovf = {8'h00};
      bins ovf    = {[8'h01:8'hFF]};
    }
    axb_cross: cross a_cp, b_cp;
  endgroup
  mult_cg cg = new();
  always @(a or b) cg.sample();

endmodule