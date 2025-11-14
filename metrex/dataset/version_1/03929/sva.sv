// SVA for binary_adder
// Bind to the DUT without modifying it
module binary_adder_sva #(parameter W=16)
(
  input  logic               clk,
  input  logic               rst_n,
  input  logic [W-1:0]       A,
  input  logic [W-1:0]       B,
  input  logic               Cin,
  input  logic [W-1:0]       Sum,
  input  logic               Cout
);
  // convenient 17-bit full sum
  logic [W:0] full_sum;
  assign full_sum = {1'b0, A} + {1'b0, B} + Cin;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Reset behavior
  assert property (@(negedge rst_n) (Sum == '0 && Cout == 1'b0))
    else $error("Outputs not cleared on reset assert");
  assert property (rst_n == 0 |-> Sum == '0 && Cout == 1'b0)
    else $error("Outputs not held at 0 during reset");

  // No X/Z on key signals when out of reset
  assert property (!$isunknown({A,B,Cin}))
    else $error("Inputs contain X/Z");
  assert property (!$isunknown({Sum,Cout}))
    else $error("Outputs contain X/Z");

  // Functional correctness (this will flag any sum/carry misalignment)
  assert property ({Cout, Sum} == full_sum)
    else $error("{Cout,Sum} != A+B+Cin");

  // Also check Sum low bits alone to isolate issues
  assert property (Sum == full_sum[W-1:0])
    else $error("Sum[W-1:0] mismatch vs A+B+Cin");

  // Glitch-free outputs between clock edges (except during reset)
  assert property (@(negedge clk) $stable({Sum,Cout}))
    else $error("Outputs changed outside posedge clk");

  // Basic functional coverage
  cover property (full_sum[W]);                       // overflow occurs
  cover property (!full_sum[W]);                      // no overflow
  cover property (Cin && (A==0) && (B==0));           // carry-in only
  cover property ((A=={W{1'b1}}) && (B=={W{1'b1}}) && Cin); // max+max+1

endmodule

bind binary_adder binary_adder_sva #(.W(16))) u_binary_adder_sva (
  .clk (clk),
  .rst_n (rst_n),
  .A (A),
  .B (B),
  .Cin (Cin),
  .Sum (Sum),
  .Cout (Cout)
);