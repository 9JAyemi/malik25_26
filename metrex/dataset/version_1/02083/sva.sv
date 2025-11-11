// SVA for the provided design. Focused, high-quality, concise checks + coverage.

package dut_sva_pkg;
  function automatic logic [31:0] byte_rev32(input logic [31:0] x);
    return {x[7:0], x[15:8], x[23:16], x[31:24]};
  endfunction
  function automatic logic [31:0] zext3(input logic a,b,cin);
    return {29'd0, a, b, cin};
  endfunction
endpackage

// byte_reverser: pure combinational equivalence
module byte_reverser_sva(input logic [31:0] in, out);
  import dut_sva_pkg::*;
  always_comb begin
    assert (out == byte_rev32(in))
      else $error("byte_reverser mismatch: out=%h exp=%h in=%h", out, byte_rev32(in), in);
    cover (in != 32'h0);
    cover (out[31:24] == in[7:0] && out[7:0] == in[31:24]);
  end
endmodule

// full_adder: arithmetic equivalence + full input-space coverage
module full_adder_sva(input logic a,b,cin, sum, carry_out);
  always_comb begin
    assert (sum == (a ^ b ^ cin));
    assert (carry_out == ((a & b) | (a & cin) | (b & cin)));
    assert ({carry_out,sum} == a + b + cin);

    cover ({a,b,cin} == 3'd0);
    cover ({a,b,cin} == 3'd1);
    cover ({a,b,cin} == 3'd2);
    cover ({a,b,cin} == 3'd3);
    cover ({a,b,cin} == 3'd4);
    cover ({a,b,cin} == 3'd5);
    cover ({a,b,cin} == 3'd6);
    cover ({a,b,cin} == 3'd7);
  end
endmodule

// functional_module: width-mismatch intent (only low nibble XORed), upper bits pass-through
module functional_module_sva(input logic [31:0] in1, out, input logic [2:0] in2);
  logic [3:0] mask4;
  assign mask4 = {in2[2], in2[2], in2[1:0]};
  always_comb begin
    assert (out[3:0]  == (in1[3:0]  ^ mask4));
    assert (out[31:4] ==  in1[31:4]);
    cover (mask4 != 4'h0);
    cover (in1[31:4] != '0);
  end
endmodule

// control_logic: end-to-end equivalence to "reverse(select ? zext3(a,b,cin) : in1)"
module control_logic_sva(input logic select,
                         input logic [31:0] in1,
                         input logic a,b,cin,
                         input logic [31:0] out);
  import dut_sva_pkg::*;
  logic [31:0] expect_out;
  always_comb begin
    expect_out = byte_rev32(select ? zext3(a,b,cin) : in1);
    assert (out == expect_out);

    // When selecting scalar inputs, only MSB byte carries {a,b,cin} in its low 3 bits; rest zero
    assert (select -> (out[31:24][2:0] == {a,b,cin}) && (out[23:0] == 24'd0));
  end
endmodule

// top_module: clocked end-to-end properties + branch/space coverage + X-prop check
module top_module_sva(input logic clk, reset,
                      input logic [31:0] in,
                      input logic a,b,cin, select,
                      input logic [31:0] out);
  import dut_sva_pkg::*;

  // Expected behavior per select
  property p_rev_from_in;
    @(posedge clk) disable iff (reset)
      !select |-> (out == byte_rev32(in));
  endproperty
  property p_rev_from_scalars;
    @(posedge clk) disable iff (reset)
      select |-> (out == byte_rev32(zext3(a,b,cin)));
  endproperty
  // No X on output when inputs known
  property p_no_x;
    @(posedge clk) disable iff (reset)
      !($isunknown({in,a,b,cin,select})) |-> !$isunknown(out);
  endproperty

  assert property (p_rev_from_in);
  assert property (p_rev_from_scalars);
  assert property (p_no_x);

  // Coverage: both branches, non-trivial data, and all 3-bit scalar combinations when selected
  cover property (@(posedge clk) disable iff (reset) !select && (in != 32'd0));
  cover property (@(posedge clk) disable iff (reset) select);
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_cov_sel_scalar_space
      cover property (@(posedge clk) disable iff (reset) select && {a,b,cin} == i[2:0]);
    end
  endgenerate
  // Toggle select to ensure both paths exercised at least once
  cover property (@(posedge clk) disable iff (reset) $changed(select));
endmodule

// Bind assertions to DUTs
bind byte_reverser      byte_reverser_sva     (.in(in), .out(out));
bind full_adder         full_adder_sva        (.a(a), .b(b), .cin(cin), .sum(sum), .carry_out(carry_out));
bind functional_module  functional_module_sva (.in1(in1), .in2(in2), .out(out));
bind control_logic      control_logic_sva     (.select(select), .in1(in1), .a(a), .b(b), .cin(cin), .out(out));
bind top_module         top_module_sva        (.clk(clk), .reset(reset), .in(in), .a(a), .b(b), .cin(cin), .select(select), .out(out));