// SVA for binary_adder + sub-blocks.
// Assumes a simulation sampling clock named 'clk' is visible at bind scope.

module ha_sva(input logic clk, input logic a,b,sum,carry);
  default clocking @(posedge clk); endclocking
  // Functional correctness
  assert property (sum == (a ^ b)) else $error("HA sum mismatch");
  assert property (carry == (a & b)) else $error("HA carry mismatch");
  // X/Z check
  assert property (!$isunknown({a,b,sum,carry})) else $error("HA X/Z detected");
  // Full truth-table coverage
  cover property (a==0 && b==0 && sum==0 && carry==0);
  cover property (a==0 && b==1 && sum==1 && carry==0);
  cover property (a==1 && b==0 && sum==1 && carry==0);
  cover property (a==1 && b==1 && sum==0 && carry==1);
endmodule

module fa_sva(input logic clk, input logic a,b,cin,sum,cout);
  default clocking @(posedge clk); endclocking
  // Functional correctness (equivalent forms)
  assert property ({cout,sum} == a + b + cin) else $error("FA add mismatch");
  assert property (sum == (a ^ b ^ cin)) else $error("FA sum mismatch");
  assert property (cout == ((a & b) | (a & cin) | (b & cin))) else $error("FA cout mismatch");
  // X/Z check
  assert property (!$isunknown({a,b,cin,sum,cout})) else $error("FA X/Z detected");
  // Carry scenarios coverage: generate, propagate, kill, simple no-carry sum
  cover property (a & b && cout);
  cover property ((a ^ b) && cin && cout);
  cover property (!(a | b) && !cin && !cout);
  cover property ((a ^ b) && !cin && sum && !cout);
endmodule

module bin_adder_sva(input logic clk, input logic [4:0] a,b,sum, input logic carry);
  default clocking @(posedge clk); endclocking
  // End-to-end correctness
  assert property ({carry,sum} == a + b) else $error("BIN add mismatch");
  // X/Z check
  assert property (!$isunknown({a,b,sum,carry})) else $error("BIN X/Z detected");
  // Key scenarios coverage
  cover property (a==5'd0 && b==5'd0 && sum==5'd0 && carry==1'b0);
  cover property (carry==1'b1);                // overflow observed
  cover property (sum==5'h1F && carry==1'b0);  // max sum without overflow
  cover property (sum==5'h00 && carry==1'b1);  // wrap-around (e.g., 16+16)
endmodule

// Bind SVA to DUTs (provide a sampling clk from your TB)
bind half_adder   ha_sva       u_ha_sva(.clk(clk), .a(a), .b(b), .sum(sum), .carry(carry));
bind full_adder   fa_sva       u_fa_sva(.clk(clk), .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));
bind binary_adder bin_adder_sva u_bin_sva(.clk(clk), .a(a), .b(b), .sum(sum), .carry(carry));