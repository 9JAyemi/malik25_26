// SVA checkers for four_bit_adder and full_adder
// Provide clk/rst_n from your environment via bind/connect.

module four_bit_adder_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic        cin,
  input logic [3:0]  sum,
  input logic        cout
);
  default clocking cb @(posedge clk); endclocking

  // Known-ness
  assert property (disable iff (!rst_n)
    !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout})
  );

  // Functional correctness: exact 5-bit addition
  assert property (disable iff (!rst_n)
    {cout,sum} == a + b + cin
  );

  // Coverage: key corner/scenario hits
  // Zero
  cover property (disable iff (!rst_n)
    a==4'h0 && b==4'h0 && cin==1'b0 && sum==4'h0 && cout==1'b0
  );
  // Kill: carry-in stops immediately
  cover property (disable iff (!rst_n)
    a==4'h0 && b==4'h0 && cin==1'b1 && sum==4'h1 && cout==1'b0
  );
  // Full propagate chain across 4 bits
  cover property (disable iff (!rst_n)
    (a^b)==4'hF && cin==1'b1 && sum==4'h0 && cout==1'b1
  );
  // Generate at MSB causing carry-out
  cover property (disable iff (!rst_n)
    a==4'h8 && b==4'h8 && cin==1'b0 && sum==4'h0 && cout==1'b1
  );
  // Max overflow
  cover property (disable iff (!rst_n)
    a==4'hF && b==4'hF && cin==1'b1 && sum==4'hF && cout==1'b1
  );
endmodule


module full_adder_sva (
  input logic clk,
  input logic rst_n,
  input logic a,
  input logic b,
  input logic cin,
  input logic sum,
  input logic cout
);
  default clocking cb @(posedge clk); endclocking

  // Known-ness
  assert property (disable iff (!rst_n)
    !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout})
  );

  // Truth table equivalence
  assert property (disable iff (!rst_n)
    sum == (a ^ b ^ cin)
  );
  assert property (disable iff (!rst_n)
    cout == ((a & b) | (a & cin) | (b & cin))
  );

  // Cover all 8 input combinations
  cover property (disable iff (!rst_n) {a,b,cin}==3'b000);
  cover property (disable iff (!rst_n) {a,b,cin}==3'b001);
  cover property (disable iff (!rst_n) {a,b,cin}==3'b010);
  cover property (disable iff (!rst_n) {a,b,cin}==3'b011);
  cover property (disable iff (!rst_n) {a,b,cin}==3'b100);
  cover property (disable iff (!rst_n) {a,b,cin}==3'b101);
  cover property (disable iff (!rst_n) {a,b,cin}==3'b110);
  cover property (disable iff (!rst_n) {a,b,cin}==3'b111);
endmodule

// Example bind (edit clk/rst_n paths to your environment):
// bind four_bit_adder four_bit_adder_sva u_four_bit_adder_sva(.clk(tb_clk), .rst_n(tb_rst_n), .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));
// bind full_adder     full_adder_sva     u_full_adder_sva    (.clk(tb_clk), .rst_n(tb_rst_n), .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));