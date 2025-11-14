// SVA checker for top_module
module top_module_sva (
  input logic        clk,
  input logic [7:0]  in,
  input logic [7:0]  anyedge,

  // internal DUT signals (bound from top_module)
  input logic [7:0]  pipe1,
  input logic [7:0]  pipe2,
  input logic [7:0]  pipe3
);

  default clocking cb @(posedge clk); endclocking
  // Wait for 2 cycles of history to avoid X/first-cycle effects
  default disable iff (!$past(1'b1,2,1'b0));

  // Pipeline stage correctness
  assert property (pipe1 == $past(in,  1, '0))
    else $error("pipe1 != past(in)");
  assert property (pipe2 == $past(pipe1,1, '0))
    else $error("pipe2 != past(pipe1)");
  assert property (pipe3 == $past(pipe2,1, '0))
    else $error("pipe3 != past(pipe2)");

  // Functional correctness vs internal pipes (logic minimization check)
  assert property (anyedge == (~pipe1 & pipe2 & ~pipe3))
    else $error("anyedge != ~(pipe1) & pipe2 & ~(pipe3)");

  // Functional correctness vs input history (independent of internals)
  assert property (anyedge == (~in & $past(in,1,'0) & ~$past(in,2,'0)))
    else $error("anyedge != ~(in) & past(in) & ~past2(in)");

  // Sanity: anyedge can only be 1 when pipe2 is 1 and pipe1/pipe3 are 0 (bitwise)
  assert property ((anyedge & ~pipe2) == '0) else $error("anyedge set when pipe2=0");
  assert property ((anyedge &  pipe1) == '0) else $error("anyedge set when pipe1=1");
  assert property ((anyedge &  pipe3) == '0) else $error("anyedge set when pipe3=1");

  // Coverage: observe at least one single-cycle pulse per bit (cause+effect)
  genvar i;
  generate
    for (i=0; i<8; i++) begin : cov_bits
      cover property ((~in[i] && $past(in[i],1,1'b0) && ~$past(in[i],2,1'b0)) && anyedge[i]);
    end
  endgenerate

  // Coverage: any bit detected
  cover property (anyedge != '0);

endmodule

// Bind into the DUT (gives the checker access to internal pipes)
bind top_module top_module_sva u_top_module_sva (
  .clk     (clk),
  .in      (in),
  .anyedge (anyedge),
  .pipe1   (pipe1),
  .pipe2   (pipe2),
  .pipe3   (pipe3)
);