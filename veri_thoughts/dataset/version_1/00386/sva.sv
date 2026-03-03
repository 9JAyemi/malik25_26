// SVA for adder_4bit
module adder_4bit_sva (
  input  logic        CLK,
  input  logic        RST,     // active-low async reset
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        CIN,
  input  logic [3:0]  SUM,
  input  logic        COUT
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RST);

  // Functional correctness: registered result equals 5-bit sum of sampled inputs
  property p_add_result;
    logic [3:0] a_s, b_s;
    logic       cin_s;
    logic [4:0] sum5_s;
    (a_s = A, b_s = B, cin_s = CIN,
     sum5_s = {1'b0,a_s} + {1'b0,b_s} + cin_s, 1'b1)
    |=> {COUT, SUM} == sum5_s;
  endproperty
  assert property (p_add_result)
    else $error("Adder result mismatch: expected {COUT,SUM} = A+B+CIN (5-bit)");

  // Outputs are never X/Z during normal operation
  assert property (!$isunknown({SUM, COUT})))
    else $error("Unknown on outputs during operation");

  // Asynchronous reset behavior: immediate clear on negedge RST
  assert property (@(negedge RST) (SUM == 4'b0 && COUT == 1'b0))
    else $error("Async reset did not clear outputs immediately");

  // Hold zero throughout reset low
  assert property (@(posedge CLK or negedge RST) (!RST) |-> (SUM == 4'b0 && COUT == 1'b0))
    else $error("Outputs non-zero while reset asserted");

  // ----------------
  // Coverage
  // ----------------

  // See both CIN values
  cover property (CIN == 1'b0);
  cover property (CIN == 1'b1);

  // See both carry-out results
  cover property (COUT == 1'b0);
  cover property (COUT == 1'b1);

  // Corner sums
  cover property (SUM == 4'h0);
  cover property (SUM == 4'hF);

  // Carry-out due to MSB generate (A[3]&B[3]) (with sampled inputs)
  property c_gen_msb;
    logic [3:0] a_s, b_s; logic cin_s; logic [4:0] sum5_s;
    (a_s=A, b_s=B, cin_s=CIN, sum5_s={1'b0,a_s}+{1'b0,b_s}+cin_s, 1)
    |=> (a_s[3] && b_s[3]) && (sum5_s[4] && COUT);
  endproperty
  cover property (c_gen_msb);

  // Carry-out from lower-bit ripple when A[3]==0, B[3]==0, CIN==0
  property c_ripple_lower;
    logic [3:0] a_s, b_s; logic cin_s; logic [4:0] sum5_s;
    (a_s=A, b_s=B, cin_s=CIN, sum5_s={1'b0,a_s}+{1'b0,b_s}+cin_s, 1)
    |=> (!a_s[3] && !b_s[3] && !cin_s) && (sum5_s[4] && COUT);
  endproperty
  cover property (c_ripple_lower);

  // Reset pulse observed (assert and deassert)
  cover property (@(negedge RST) 1);
  cover property (@(posedge RST) 1);

endmodule

// Bind into DUT
bind adder_4bit adder_4bit_sva sva_i (
  .CLK (CLK),
  .RST (RST),
  .A   (A),
  .B   (B),
  .CIN (CIN),
  .SUM (SUM),
  .COUT(COUT)
);