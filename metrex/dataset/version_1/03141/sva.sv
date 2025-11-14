// SVA for top_module. Bind this file to the DUT.
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [3:0]  sel,
  input  logic [7:0]  out,
  input  logic [8:0]  sum
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  function automatic [7:0] f_exp_out (logic [3:0] s, logic [7:0] d_i, logic [7:0] a_i, logic [7:0] b_i);
    case (s)
      4'h0: f_exp_out = d_i;
      4'h1: f_exp_out = a_i;
      4'h2: f_exp_out = b_i;
      4'h3: f_exp_out = 8'h00;
      default: f_exp_out = 8'h00;
    endcase
  endfunction

  function automatic [8:0] f_exp_sum (logic [7:0] a_i, logic [7:0] b_i);
    automatic logic [8:0] add9;
    add9    = {1'b0, a_i} + {1'b0, b_i};      // 9-bit add
    f_exp_sum = (add9 + 9'h034) >> 1;         // add const (9-bit wrap) then drop LSB
  endfunction

  // X/Z checks
  assert property (!$isunknown({sel, d, a, b}))) else $error("Inputs contain X/Z");
  assert property (!$isunknown({out, sum})))      else $error("Outputs contain X/Z");

  // Functional correctness
  assert property (out === f_exp_out(sel, d, a, b))
    else $error("Mux output mismatch");

  assert property (sum === f_exp_sum(a, b))
    else $error("Sum output mismatch");

  // Stability: if drivers are stable, outputs remain stable
  assert property ($stable({sel, d, a, b}) |-> $stable(out));
  assert property ($stable({a, b})         |-> $stable(sum));

  // Functional coverage
  cover property (sel == 4'h0 && out == d);
  cover property (sel == 4'h1 && out == a);
  cover property (sel == 4'h2 && out == b);
  cover property (sel == 4'h3 && out == 8'h00);
  cover property (sel >  4'd3 && out == 8'h00);         // default case

  // Adder carry-out observed
  cover property (({1'b0, a} + {1'b0, b})[8]);

  // sum_temp LSB (before >>1) both parities observed
  cover property (((( {1'b0,a} + {1'b0,b} ) + 9'h034) & 9'h001) == 1'b0);
  cover property (((( {1'b0,a} + {1'b0,b} ) + 9'h034) & 9'h001) == 1'b1);

  // Extremes of sum after >>1
  cover property (sum == 9'd0);
  cover property (sum == 9'd255);
endmodule

// Bind into the DUT
bind top_module top_module_sva u_top_module_sva (
  .clk  (clk),
  .reset(reset),
  .d    (d),
  .a    (a),
  .b    (b),
  .sel  (sel),
  .out  (out),
  .sum  (sum)
);