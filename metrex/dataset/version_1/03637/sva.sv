// SVA for top_module and submodules (concise, quality-focused)
`ifndef TOP_SVA
`define TOP_SVA

module top_module_sva
(
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        select,
  input  logic [31:0] sum,
  input  logic [31:0] adder_out,
  input  logic        mux_out
);
  // Functional equivalence and X-propagation
  assert property (@(*) sum == (select ? adder_out : {31'b0, mux_out}));
  assert property (@(*) !$isunknown({a,b,select}) |-> !$isunknown(sum));

  // Path coverage
  cover  property (@(*)  select && (sum == adder_out));
  cover  property (@(*) !select && (sum[31:1] == '0) && (sum[0] == mux_out));

  // Select edge coverage
  cover  property (@(posedge select) 1);
  cover  property (@(negedge select) 1);
endmodule

module adder_sva
(
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [31:0] sum
);
  // Given cin=0 and no carry chain, adder_out must be bitwise XOR
  assert property (@(*) sum == (a ^ b));
  assert property (@(*) !$isunknown({a,b}) |-> !$isunknown(sum));

  // Basic activity coverage
  cover  property (@(*) (sum != 32'h0) && (sum != 32'hFFFF_FFFF));
endmodule

module mux_sva
(
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        c,
  input  logic        w
);
  assert property (@(*) w == (c ? b[0] : a[0]));
  assert property (@(*) !$isunknown({a[0],b[0],c}) |-> !$isunknown(w));

  cover  property (@(*)  c && (w == b[0]));
  cover  property (@(*) !c && (w == a[0]));
endmodule

module full_adder_sva
(
  input  logic a, b, cin,
  input  logic sum, cout
);
  assert property (@(*) sum  == (a ^ b ^ cin));
  assert property (@(*) cout == ((a & b) | (b & cin) | (a & cin)));

  // Carry generate/propagate coverage
  cover  property (@(*) (a & b));             // generate
  cover  property (@(*) (cin & (a ^ b)));     // propagate
endmodule

// Bind assertions into DUT
bind top_module top_module_sva u_top_module_sva(.a(a), .b(b), .select(select), .sum(sum),
                                                .adder_out(adder_out), .mux_out(mux_out));
bind adder      adder_sva      u_adder_sva(.*);
bind mux        mux_sva        u_mux_sva(.*);
bind full_adder full_adder_sva u_full_adder_sva(.*);

`endif