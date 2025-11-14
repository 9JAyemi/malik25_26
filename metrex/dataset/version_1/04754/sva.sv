// SVA for top_module
// Provide a TB clock/reset and bind this checker to the DUT instance.
// Replace tb_clk/tb_rst_n in the bind with your environment signals.

module top_module_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        a,
  input  logic        b,
  input  logic        sel_b1,
  input  logic        sel_b2,
  input  logic [7:0]  in,
  input  logic [7:0]  out,
  input  logic        mux_out,   // internal net
  input  logic [7:0]  and_out    // internal net
);
  localparam logic [7:0] MASK = 8'hE3;

  function automatic bit known_inputs();
    return !$isunknown({a,b,sel_b1,sel_b2,in});
  endfunction

  // Mux correctness
  assert property (@(posedge clk) disable iff (!rst_n)
    known_inputs() |-> mux_out == ((sel_b1 & sel_b2) ? b : a)
  ) else $error("mux_out mismatch");

  // AND mask correctness
  assert property (@(posedge clk) disable iff (!rst_n)
    known_inputs() |-> and_out == (in & MASK)
  ) else $error("and_out != in & MASK");

  // Functional output relation (as coded)
  assert property (@(posedge clk) disable iff (!rst_n)
    known_inputs() |-> out == ((mux_out == a) ? in : and_out)
  ) else $error("out functional relation failed");

  // Derived behaviors (stronger intent checks)
  assert property (@(posedge clk) disable iff (!rst_n)
    known_inputs() && !(sel_b1 & sel_b2) |-> out == in
  ) else $error("out must be in when sel_b1&sel_b2==0");

  assert property (@(posedge clk) disable iff (!rst_n)
    known_inputs() && (sel_b1 & sel_b2) && (a == b) |-> out == in
  ) else $error("out must be in when selecting b and a==b");

  assert property (@(posedge clk) disable iff (!rst_n)
    known_inputs() && (sel_b1 & sel_b2) && (a != b) |-> out == (in & MASK)
  ) else $error("out must be masked when selecting b and a!=b");

  // Output can only be in or masked-in when inputs are known
  assert property (@(posedge clk) disable iff (!rst_n)
    known_inputs() |-> ((out == in) || (out == (in & MASK)))
  ) else $error("out takes illegal value");

  // No X/Z on outputs when inputs are known
  assert property (@(posedge clk) disable iff (!rst_n)
    known_inputs() |-> !$isunknown({mux_out,and_out,out})
  ) else $error("Unknowns on outputs with known inputs");

  // Minimal, high-value coverage
  cover property (@(posedge clk)
    known_inputs() && !(sel_b1 & sel_b2) && out == in
  );

  cover property (@(posedge clk)
    known_inputs() && (sel_b1 & sel_b2) && (a == b) && out == in
  );

  cover property (@(posedge clk)
    known_inputs() && (sel_b1 & sel_b2) && (a != b) && (in[4+:3] != 3'b000) && out == (in & MASK)
  );

  cover property (@(posedge clk)
    known_inputs() && (sel_b1 & sel_b2) && (a != b) ##1 !(sel_b1 & sel_b2)
  );

endmodule

// Bind example (place in TB scope where tb_clk/tb_rst_n are visible):
// bind top_module top_module_sva u_top_module_sva (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .a(a), .b(b), .sel_b1(sel_b1), .sel_b2(sel_b2),
//   .in(in), .out(out), .mux_out(mux_out), .and_out(and_out)
// );