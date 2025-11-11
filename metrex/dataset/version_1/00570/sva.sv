// SVA checker for adder_4bit_carry
module adder_4bit_carry_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic        cin,
  input logic [3:0]  sum,
  input logic        cout
);
  logic [4:0] sum5;
  assign sum5 = $unsigned(a) + $unsigned(b) + $unsigned(cin);

  // Functional correctness when inputs are known
  assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown({a,b,cin}) |-> {cout,sum} == sum5
  ) else $error("adder mismatch: a=%0h b=%0h cin=%0b got {cout,sum}=%0h exp=%0h",
                a,b,cin,{cout,sum},sum5);

  // No X/Z on outputs with known inputs
  assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout})
  ) else $error("adder produced X/Z on outputs with known inputs");

  // Purely combinational behavior (no hidden state)
  assert property (@(posedge clk) disable iff (!rst_n)
    $stable({a,b,cin}) |-> $stable({sum,cout})
  ) else $error("non-combinational behavior detected");

  // Concise, full-result coverage across all 5-bit sums
  covergroup cg_sum5 @(posedge clk);
    option.per_instance = 1;
    cp_sum5: coverpoint sum5 { bins all[] = {[0:31]}; }
    cp_cin:  coverpoint cin  { bins zero = {0}; bins one = {1}; }
    cp_cout: coverpoint cout { bins zero = {0}; bins one = {1}; }
  endgroup
  cg_sum5 cg = new;

  // Key scenario covers
  cover property (@(posedge clk) disable iff (!rst_n)
    (a==4'h0 && b==4'h0 && cin==1'b0 && sum==4'h0 && cout==1'b0));
  cover property (@(posedge clk) disable iff (!rst_n)
    (a==4'hF && b==4'hF && cin==1'b1 && sum==4'hF && cout==1'b1));
  cover property (@(posedge clk) disable iff (!rst_n)
    (a==4'hF && b==4'h1 && cin==1'b0 && sum==4'h0 && cout==1'b1));
endmodule

// Example bind from your TB:
// bind adder_4bit_carry adder_4bit_carry_sva u_sva (.*, .clk(tb_clk), .rst_n(tb_rst_n));