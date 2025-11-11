// SVA checkers and binds for the provided design

// Top-level checker
module top_module_sva_checker (
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        sel,
  input  logic [31:0] sum,
  input  logic [7:0]  adder1_out,
  input  logic [7:0]  adder2_out,
  input  logic [15:0] adder3_out,
  input  logic [3:0]  mux_out
);
  // Functional correctness (combinational)
  always_comb begin
    assert (sum == (sel ? ({mux_out, a[31:23]} + b) : (a + b)))
      else $error("top: sum mismatch");

    // Internal adders consistency w.r.t their inputs
    assert (adder1_out == (a[7:0]   + b[7:0]))   else $error("top: adder1_out mismatch");
    assert (adder2_out == (a[15:8]  + b[15:8]))  else $error("top: adder2_out mismatch");
    assert (adder3_out == { (a[31:24] + b[31:24]), (a[23:16] + b[23:16]) })
      else $error("top: adder3_out mismatch (bytewise)");

    // X-prop hygiene
    if (!$isunknown({a,b,sel})) begin
      assert (!$isunknown(sum)) else $error("top: sum is X/Z");
      assert (!$isunknown({adder1_out,adder2_out,adder3_out,mux_out})) else $error("top: internal X/Z");
    end

    // Targeted coverage
    cover (sel == 0);
    cover (sel == 1);
    cover (sel && mux_out == 4'b0001);
    cover (sel && mux_out == 4'b0010);
    cover (sel && mux_out == 4'b0100);
    cover (sel && mux_out == 4'b1000);
    cover (a == 32'hFFFF_FFFF && b == 32'h0000_0001); // wrap
    cover (a == 32'h0000_0000 && b == 32'h0000_0000); // zero
  end
endmodule

// mux_3_4 checker
module mux_3_4_sva_checker (
  input  logic a,
  input  logic b,
  input  logic c,
  input  logic sel,
  input  logic [3:0] y
);
  always_comb begin
    assert (y[0] == ((~sel & ~a) & b)) else $error("mux: y[0] expr mismatch");
    assert (y[1] == ((~sel &  a) & c)) else $error("mux: y[1] expr mismatch");
    assert (y[2] == (( sel & ~a) & b)) else $error("mux: y[2] expr mismatch");
    assert (y[3] == (( sel &  a) & c)) else $error("mux: y[3] expr mismatch");
    assert ($onehot0(y)) else $error("mux: y not onehot0");

    if (!$isunknown({a,b,c,sel})) assert (!$isunknown(y)) else $error("mux: y is X/Z");

    cover (sel==0);
    cover (sel==1);
    cover (y[0]);
    cover (y[1]);
    cover (y[2]);
    cover (y[3]);
  end
endmodule

// add_8 checker
module add_8_sva_checker (
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [7:0] sum
);
  always_comb begin
    assert (sum == (a + b)) else $error("add_8: sum mismatch");
    if (!$isunknown({a,b})) assert (!$isunknown(sum)) else $error("add_8: sum is X/Z");

    cover (sum < a);   // wrap occurred
    cover (sum >= a);  // no wrap
    cover (sum == 8'h00);
    cover (sum == 8'hFF);
  end
endmodule

// add_16 checker (bytewise add as implemented)
module add_16_sva_checker (
  input  logic [15:0] a,
  input  logic [15:0] b,
  input  logic [15:0] sum
);
  always_comb begin
    assert (sum[7:0]  == (a[7:0]  + b[7:0]))  else $error("add_16: low byte mismatch");
    assert (sum[15:8] == (a[15:8] + b[15:8])) else $error("add_16: high byte mismatch");
    assert (sum == { (a[15:8] + b[15:8]), (a[7:0] + b[7:0]) })
      else $error("add_16: full bytewise mismatch");

    if (!$isunknown({a,b})) assert (!$isunknown(sum)) else $error("add_16: sum is X/Z");

    cover (sum[7:0]  < a[7:0]);   // low byte wrap
    cover (sum[15:8] < a[15:8]);  // high byte wrap
    cover (sum[15:8] == 8'h00 && sum[7:0] == 8'h00);
  end
endmodule

// Binds
bind mux_3_4 mux_3_4_sva_checker i_mux_3_4_sva (.*);
bind add_8   add_8_sva_checker   i_add_8_sva   (.*);
bind add_16  add_16_sva_checker  i_add_16_sva  (.*);

// Bind to top with internal nets
bind top_module top_module_sva_checker i_top_sva (
  .a(a),
  .b(b),
  .sel(sel),
  .sum(sum),
  .adder1_out(adder1_out),
  .adder2_out(adder2_out),
  .adder3_out(adder3_out),
  .mux_out(mux_out)
);