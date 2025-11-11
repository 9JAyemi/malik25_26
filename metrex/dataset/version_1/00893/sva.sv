// SVA checker for top_module
module top_module_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  in0,
  input logic [3:0]  in1,
  input logic        DIR,
  input logic [1:0]  AMT,
  input logic        eq,
  input logic        gt,
  input logic        lt,
  input logic [3:0]  out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // No X/Z on key signals
  a_no_x:        assert property (!$isunknown({in0,in1,DIR,AMT,out,eq,gt,lt}));

  // Shifter behavior matches spec
  a_shift_func:  assert property (out == (DIR ? (in0 >> AMT) : (in0 << AMT)));

  // Passthrough when AMT == 0
  a_amt0_pass:   assert property ((AMT == 2'd0) |-> (out == in0));

  // Comparator outputs match relation of out vs in1
  a_cmp_map:     assert property ({eq,gt,lt} == { (out == in1), (out > in1), (out < in1) });

  // Exactly one comparator bit set
  a_onehot_res:  assert property ($onehot({eq,gt,lt}));

  // Coverage: exercise DIR/AMT space and all comparator outcomes
  covergroup cg @(posedge clk);
    dir: coverpoint DIR;
    amt: coverpoint AMT { bins all[] = {0,1,2,3}; }
    res: coverpoint {eq,gt,lt} {
      bins beq = {3'b100};
      bins bgt = {3'b010};
      bins blt = {3'b001};
    }
    cross dir, amt;
  endgroup
  cg cg_i = new();

  // Corner covers
  c_lshift_max:  cover property (DIR == 1'b0 && AMT == 2'd3);
  c_rshift_max:  cover property (DIR == 1'b1 && AMT == 2'd3);
  c_eq:          cover property (eq);
  c_gt:          cover property (gt);
  c_lt:          cover property (lt);
endmodule

// Example bind (hook up clk/rst and DUT signals as available in your env):
// bind top_module top_module_sva u_sva (
//   .clk   (clk),
//   .rst_n (rst_n),
//   .in0   (in0),
//   .in1   (in1),
//   .DIR   (DIR),
//   .AMT   (AMT),
//   .eq    (eq),
//   .gt    (gt),
//   .lt    (lt),
//   .out   (out)
// );