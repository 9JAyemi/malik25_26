// SVA checker for four_bit_selector
module four_bit_selector_sva(input logic clk, input logic rst_n,
                             input logic [3:0] a,
                             input logic [1:0] o);

  default clocking @(posedge clk); endclocking

  // Functional correctness (single concise spec)
  a_func_ok: assert property (disable iff (!rst_n)
                              o == ((a < 5) ? a[1:0] : (a >> 2)[3:2]))
    else $error("four_bit_selector: functional mismatch: a=%0d o=%0d", a, o);

  // Strengthen else-branch intent (for this 4-bit design, else must be zero)
  a_else_zero: assert property (disable iff (!rst_n)
                                (a >= 5) |-> (o == 2'b00))
    else $error("four_bit_selector: else-branch not zero for a>=5");

  // Knownness: if input is known, output must be known
  a_no_x_propagation: assert property (disable iff (!rst_n)
                                       !$isunknown(a) |-> !$isunknown(o))
    else $error("four_bit_selector: X/Z detected on o with known a");

  // Basic branch coverage
  c_small_range: cover property (disable iff (!rst_n) (a < 5) && (o == a[1:0]));
  c_large_range: cover property (disable iff (!rst_n) (a >= 5) && (o == 2'b00));

  // Boundary and extreme value coverage
  c_a_eq_4: cover property (disable iff (!rst_n) a == 4 && o == 2'b00);
  c_a_eq_5: cover property (disable iff (!rst_n) a == 5 && o == 2'b00);
  c_a_eq_0: cover property (disable iff (!rst_n) a == 0 && o == 2'b00);
  c_a_eq_15: cover property (disable iff (!rst_n) a == 15 && o == 2'b00);

endmodule

// Bind example (provide a free-running clk and rst_n in your TB)
// bind four_bit_selector four_bit_selector_sva u_four_bit_selector_sva(.clk(clk), .rst_n(rst_n), .a(a), .o(o));