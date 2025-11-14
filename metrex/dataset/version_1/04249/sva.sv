// SystemVerilog Assertions for mul16 and top_module
// Focused, concise, bound to DUT without modifying RTL.

module mul16_sva(input logic [15:0] a, b,
                 input logic [31:0] result);
  always_comb begin
    assert (!$isunknown({a,b})) else $error("mul16: X/Z on inputs");
    assert (result === (a * b))
      else $error("mul16: result mismatch a=%0h b=%0h got=%0h exp=%0h", a, b, result, (a*b));
    // basic coverage
    cover (a==16'd0 && b==16'd0);
    cover (a==16'hFFFF && b==16'hFFFF);
  end
endmodule

module top_module_sva(input logic [31:0] a, b,
                      input logic        enable,
                      input logic [31:0] result,
                      input logic [31:0] mul_low,
                      input logic [31:0] mul_high);
  always_comb begin
    assert (!$isunknown({a,b,enable})) else $error("top: X/Z on inputs");

    // sub-multiply correctness
    assert (mul_low  === (a[15:0]  * b[15:0]))  else $error("top: mul_low mismatch");
    assert (mul_high === (a[31:16] * b[31:16])) else $error("top: mul_high mismatch");

    // output behavior (note: 64->32 truncation => LSBs kept)
    if (enable) begin
      assert (result === mul_low)
        else $error("top: result must equal mul_low when enable=1 (upper 32 bits truncated)");
    end else begin
      assert (result === 32'd0) else $error("top: result must be 0 when enable=0");
    end

    // coverage: exercise both paths and truncation scenario
    cover (!enable);
    cover (enable && (mul_high != 32'd0)); // demonstrates dropped upper 32 bits
    cover (enable && (mul_low  == 32'd0));
  end
endmodule

bind mul16      mul16_sva      u_mul16_sva      (.a(a), .b(b), .result(result));
bind top_module top_module_sva u_top_module_sva (.a(a), .b(b), .enable(enable),
                                                 .result(result),
                                                 .mul_low(mul_low), .mul_high(mul_high));